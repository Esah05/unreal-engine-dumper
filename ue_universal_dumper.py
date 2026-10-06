import argparse
import json
import re
import struct
import sys

import pymem
import pymem.process

KNOWN = {
    "Class", "Function", "Package", "ObjectProperty", "IntProperty",
    "FloatProperty", "BoolProperty", "StructProperty", "ArrayProperty",
    "NameProperty", "ByteProperty", "Const", "Enum", "ScriptStruct", "State",
    "StrProperty", "ClassProperty", "InterfaceProperty", "MapProperty",
    "DelegateProperty", "MetaData", "Texture2D", "StaticMesh", "Material",
    "SkeletalMesh", "World", "Level", "BlueprintGeneratedClass",
    "DelegateFunction", "UserDefinedStruct", "MaterialInstanceConstant",
    "ObjectRedirector", "SoundWave", "AnimSequence",
}
NAME_OFFS = (0x10, 0x18, 0x0C, 0x14, 0x08, 0x1C, 0x20, 0x04)
OBJECT_PROP_TYPES = (
    "ObjectProperty", "ClassProperty", "ComponentProperty", "InterfaceProperty",
    "WeakObjectProperty", "LazyObjectProperty", "SoftObjectProperty",
    "SoftClassProperty", "ObjectPtrProperty", "AssetObjectProperty",
    "AssetClassProperty",
)
CLASS_OK_FOR_OUTER = ("Class", "ScriptStruct", "Function", "BlueprintGeneratedClass",
                      "WidgetBlueprintGeneratedClass", "AnimBlueprintGeneratedClass",
                      "UserDefinedStruct")
PREFERRED_PKG = ("Core.", "Engine.", "/Script/", "UnrealScript")

# (Klassen-Fallbacks, Member-Fallbacks) - fuer ESP/Tools meist relevant
KEY_MEMBERS = [
    (("Actor",), ("Location",)),
    (("Actor",), ("Rotation",)),
    (("Actor",), ("Owner",)),
    (("Actor",), ("RootComponent",)),
    (("SceneComponent",), ("RelativeLocation",)),
    (("SceneComponent",), ("RelativeRotation",)),
    (("SceneComponent",), ("ComponentToWorld",)),
    (("Pawn",), ("Controller",)),
    (("Pawn",), ("PlayerState",)),
    (("Pawn",), ("Health",)),
    (("Character",), ("Mesh",)),
    (("Character",), ("CharacterMovement",)),
    (("Controller",), ("Pawn",)),
    (("PlayerController",), ("PlayerCamera", "PlayerCameraManager")),
    (("PlayerController",), ("AcknowledgedPawn",)),
    (("Camera", "PlayerCamera", "PlayerCameraManager"), ("CameraCache", "CameraCachePrivate")),
    (("GameEngine", "Engine"), ("GamePlayers", "GameInstance")),
    (("GameInstance",), ("LocalPlayers",)),
    (("LocalPlayer", "Player"), ("Actor", "PlayerController")),
    (("World",), ("PersistentLevel",)),
    (("World",), ("OwningGameInstance",)),
    (("World",), ("GameState",)),
    (("World",), ("Levels",)),
]


def expected_sizes(ps):
    """Bekannte Actor-Properties mit ihrer ElementSize (zur Layout-Erkennung)."""
    return {"Owner": ps, "Instigator": ps, "RootComponent": ps, "Location": 12,
            "Rotation": 12, "CustomTimeDilation": 4, "InitialLifeSpan": 4,
            "NetUpdateFrequency": 4, "DrawScale": 4, "Tag": 8, "Role": 1,
            "RemoteRole": 1}


STRUCT_SIZES = {"Guid": (16,), "LinearColor": (16,), "Color": (4,), "Vector2D": (8, 16),
                "Vector": (12, 24), "Rotator": (12, 24), "Quat": (16, 32)}


def log(*a):
    print(*a, flush=True)


# ----------------------------------------------------------------------------
# Prozess / PE
# ----------------------------------------------------------------------------
class Proc:
    def __init__(self, exe=None, pid=None):
        self.pm = pymem.Pymem(pid if pid else exe)
        if exe:
            mod = pymem.process.module_from_name(self.pm.process_handle, exe)
        else:
            mod = list(pymem.process.enum_process_module(self.pm.process_handle))[0]
        self.exe = exe or "pid%d" % pid
        self.base, self.size = mod.lpBaseOfDll, mod.SizeOfImage
        hdr = self.read(self.base, 0x1000)
        pe = struct.unpack_from("<I", hdr, 0x3C)[0]
        machine = struct.unpack_from("<H", hdr, pe + 4)[0]
        nsec = struct.unpack_from("<H", hdr, pe + 6)[0]
        optsz = struct.unpack_from("<H", hdr, pe + 20)[0]
        self.ps = 8 if machine == 0x8664 else 4
        self.fmt = "<Q" if self.ps == 8 else "<I"
        self.ch = "Q" if self.ps == 8 else "I"
        self.hi = 0x7FFFFFFFFFFF if self.ps == 8 else 0xBFFF0000
        self.sections = []
        off = pe + 24 + optsz
        for _ in range(nsec):
            name = hdr[off:off + 8].rstrip(b"\0").decode(errors="ignore")
            vsize, rva = struct.unpack_from("<II", hdr, off + 8)
            chars = struct.unpack_from("<I", hdr, off + 36)[0]
            self.sections.append((name, rva, vsize, chars))
            off += 40
        self.ptrs = []

    def read(self, addr, n):
        try:
            return self.pm.read_bytes(addr, n)
        except Exception:
            return None

    def read_big(self, addr, size, chunk=0x10000):
        out = bytearray()
        for o in range(0, size, chunk):
            n = min(chunk, size - o)
            b = self.read(addr + o, n)
            out += b if b else bytes(n)
        return bytes(out)

    def ptr(self, a):
        if a is None:
            return None
        b = self.read(a, self.ps)
        return struct.unpack(self.fmt, b)[0] if b else None

    def valid(self, v):
        return v is not None and 0x10000 <= v < self.hi

    def in_image(self, v):
        return v is not None and self.base <= v < self.base + self.size

    def load(self):
        """Liest alle beschreibbaren Sektionen und merkt sich nur gueltige Zeiger
        samt den zwei folgenden Woertern (fuer TArray-Num/Max-Pruefungen)."""
        lo, hi, ps = 0x10000, self.hi, self.ps
        ptrs = []
        for name, rva, vsize, ch in self.sections:
            if not ch & 0x80000000 or name in (".rsrc", ".reloc"):
                continue
            base = self.base + rva
            buf = self.read_big(base, vsize)
            n = len(buf) // ps
            vals = struct.unpack("<%d%s" % (n, self.ch), buf[:n * ps])
            for i, v in enumerate(vals):
                if lo <= v < hi:
                    ptrs.append((base + i * ps, v,
                                 vals[i + 1] if i + 1 < n else 0,
                                 vals[i + 2] if i + 2 < n else 0))
        self.ptrs = ptrs

    def refs_to(self, targets):
        """{Ziel: [RVA der globalen Zeiger auf Ziel]}"""
        out = {}
        for addr, v, _, _ in self.ptrs:
            if v in targets:
                out.setdefault(v, []).append(addr - self.base)
        return out


# ----------------------------------------------------------------------------
# Namen (GNames) - drei Varianten
# ----------------------------------------------------------------------------
def decode(buf):
    if len(buf) < 2:
        return None
    if buf[1] == 0 and buf[0] != 0:  # UTF-16
        end = 0
        while end + 1 < len(buf) and (buf[end] or buf[end + 1]):
            end += 2
        s = buf[:end].decode("utf-16-le", "ignore")
    else:
        end = buf.find(b"\0")
        s = buf[: end if end >= 0 else len(buf)].decode("latin-1")
    return s if s.isprintable() else None


def read_name(P, entry, off):
    for n in (0x80, 0x40, 0x20):
        b = P.read(entry + off, n)
        if b:
            return decode(b)
    return None


class NameBase:
    mode = "?"
    num = 0

    def get(self, i):
        raise NotImplementedError

    def items(self):
        for i in range(self.num):
            s = self.get(i)
            if s is not None:
                yield i, s

    def info(self, P):
        raise NotImplementedError


class ArrayNames(NameBase):
    """TArray<FNameEntry*> (UE1-3, UE4 < 4.11)"""
    mode = "TArray<FNameEntry*>"

    def __init__(self, P, addr, indirect, data, num, off):
        self.P, self.addr, self.indirect = P, addr, indirect
        self.data, self.num, self.off = data, num, off
        self.cache = {}

    def get(self, i):
        if i is None or i < 0 or i >= self.num:
            return None
        s = self.cache.get(i)
        if s is None:
            e = self.P.ptr(self.data + i * self.P.ps)
            if not self.P.valid(e):
                return None
            s = read_name(self.P, e, self.off)
            if s is not None:
                self.cache[i] = s
        return s

    def info(self, P):
        return {"mode": self.mode, "rva": hex(self.addr - P.base), "deref": self.indirect,
                "count": self.num, "entry_name_offset": hex(self.off)}


class ChunkedNames(NameBase):
    """TNameEntryArray (UE4.11 - 4.22): FNameEntry** Chunks[128], je 16384 Eintraege"""
    mode = "TNameEntryArray (chunked)"
    PER = 16384

    def __init__(self, P, slot, deref, base, off):
        self.P, self.slot, self.deref, self.base, self.off = P, slot, deref, base, off
        self.cache = {}
        n = 0
        for ci in range(128):
            c = P.ptr(base + ci * P.ps)
            if not P.valid(c):
                break
            raw = P.read_big(c, self.PER * P.ps)
            vals = struct.unpack("<%d%s" % (self.PER, P.ch), raw)
            cnt = next((k for k, v in enumerate(vals) if not v), self.PER)
            n += cnt
            if cnt < self.PER:
                break
        self.num = n

    def get(self, i):
        if i is None or i < 0 or i >= self.num:
            return None
        s = self.cache.get(i)
        if s is None:
            P = self.P
            c = P.ptr(self.base + (i // self.PER) * P.ps)
            if not P.valid(c):
                return None
            e = P.ptr(c + (i % self.PER) * P.ps)
            if not P.valid(e):
                return None
            s = read_name(P, e, self.off)
            if s is not None:
                self.cache[i] = s
        return s

    def info(self, P):
        return {"mode": self.mode, "slot_rva": hex(self.slot - P.base), "deref": self.deref,
                "count": self.num, "entry_name_offset": hex(self.off)}


class PoolNames(NameBase):
    """FNamePool (UE4.23+ / UE5). Name-ID = (Block << 16) | (Offset / 2)"""
    mode = "FNamePool"
    num = 1 << 30

    def __init__(self, P, blocks_addr):
        self.P, self.blocks = P, blocks_addr
        self.cache = {}
        self.count = None

    def get(self, i):
        if i is None or i < 0:
            return None
        s = self.cache.get(i)
        if s is not None:
            return s
        P = self.P
        blk, off = i >> 16, (i & 0xFFFF) * 2
        if blk >= 8192:
            return None
        bp = P.ptr(self.blocks + blk * P.ps)
        if not P.valid(bp):
            return None
        h = P.read(bp + off, 2)
        if not h:
            return None
        h = struct.unpack("<H", h)[0]
        ln, wide = h >> 6, h & 1
        if ln == 0 or ln > 1024:
            return None
        raw = P.read(bp + off + 2, ln * (2 if wide else 1))
        if not raw:
            return None
        s = raw.decode("utf-16-le" if wide else "latin-1", "ignore")
        self.cache[i] = s
        return s

    def items(self):
        P, n = self.P, 0
        for blk in range(8192):
            bp = P.ptr(self.blocks + blk * P.ps)
            if not P.valid(bp):
                break
            data = P.read_big(bp, 0x20000)
            off = 0
            while off + 2 <= len(data):
                h = struct.unpack_from("<H", data, off)[0]
                ln, wide = h >> 6, h & 1
                if ln == 0:
                    break
                sz = ln * (2 if wide else 1)
                raw = data[off + 2: off + 2 + sz]
                n += 1
                yield (blk << 16) | (off // 2), raw.decode("utf-16-le" if wide else "latin-1", "ignore")
                off += (2 + sz + 1) & ~1
        self.count = n

    def info(self, P):
        return {"mode": self.mode, "blocks_rva": hex(self.blocks - P.base),
                "pool_rva_guess": hex(self.blocks - (P.ps + 8)),
                "id_scheme": "(block<<16)|(byteoffset/2)"}


def tarray_candidates(P, lo, hi, indirect):
    """TArray = {T* Data; INT Num; INT Max}. Liefert (Adresse, Data, Num)."""
    ps = P.ps
    for addr, val, w1, w2 in P.ptrs:
        if not indirect:
            if ps == 8:
                num, mx = w1 & 0xFFFFFFFF, w1 >> 32
            else:
                num, mx = w1, w2
            if lo < num < hi and mx >= num:
                yield addr, val, num
        else:
            if P.in_image(val):
                continue
            b = P.read(val, ps + 8)
            if not b or len(b) < ps + 8:
                continue
            data = struct.unpack_from(P.fmt, b, 0)[0]
            num, mx = struct.unpack_from("<ii", b, ps)
            if P.valid(data) and lo < num < hi and mx >= num:
                yield addr, data, num


def find_name_pool(P):
    seen = set()
    for addr, v, w1, _ in P.ptrs:
        if v in seen or P.in_image(v):
            continue
        seen.add(v)
        if w1 and not P.valid(w1):  # Blocks[1] muss Zeiger oder 0 sein
            continue
        b = P.read(v, 24)
        if not b or len(b) < 24:
            continue
        h0 = struct.unpack_from("<H", b, 0)[0]
        if h0 >> 6 != 4 or h0 & 1 or b[2:6] != b"None":
            continue
        h1 = struct.unpack_from("<H", b, 6)[0]
        if h1 >> 6 != 12 or h1 & 1 or b[8:20] != b"ByteProperty":
            continue
        return PoolNames(P, addr)
    return None


def find_name_array(P):
    for indirect in (False, True):
        for addr, data, num in tarray_candidates(P, 1000, 2_000_000, indirect):
            e0, e1 = P.ptr(data), P.ptr(data + P.ps)
            if not (P.valid(e0) and P.valid(e1)):
                continue
            for off in NAME_OFFS:
                if read_name(P, e0, off) == "None" and read_name(P, e1, off) == "ByteProperty":
                    return ArrayNames(P, addr, indirect, data, num, off)
    return None


def find_name_chunked(P):
    seen = set()
    for addr, v, _, _ in P.ptrs:
        for deref in (False, True):
            if deref:
                if P.in_image(v) or v in seen:
                    continue
                seen.add(v)
                base, c0 = v, P.ptr(v)
            else:
                base, c0 = addr, v
            if not P.valid(c0) or P.in_image(c0):
                continue
            e = P.read(c0, 2 * P.ps)
            if not e or len(e) < 2 * P.ps:
                continue
            e0, e1 = struct.unpack("<2%s" % P.ch, e)
            if not (P.valid(e0) and P.valid(e1)):
                continue
            for off in NAME_OFFS:
                if read_name(P, e0, off) == "None" and read_name(P, e1, off) == "ByteProperty":
                    return ChunkedNames(P, addr, deref, base, off)
    return None


def find_names(P):
    return find_name_pool(P) or find_name_array(P) or find_name_chunked(P)


# ----------------------------------------------------------------------------
# GObjects + Layout
# ----------------------------------------------------------------------------
class Objects:
    def __init__(self, P, names, arr):
        self.P, self.names, self.arr = P, names, arr
        self.num = len(arr)
        self.set = set(v for v in arr if v)
        self.cache, self.L = {}, {}
        self.classes, self.structs, self.inst = {}, {}, {}
        self._members, self._isa = {}, {}

    # --- Rohzugriff
    def blob(self, o):
        b = self.cache.get(o)
        if b is None:
            if len(self.cache) > 80000:
                self.cache.clear()
            b = b""
            for n in (0x180, 0x100, 0x80):
                b = self.P.read(o, n)
                if b:
                    break
            b = self.cache[o] = b or b""
        return b

    def pt(self, o, off):
        if not o or off is None:
            return None
        b = self.blob(o)
        return struct.unpack_from(self.P.fmt, b, off)[0] if len(b) >= off + self.P.ps else None

    def i32(self, o, off):
        if not o or off is None:
            return None
        b = self.blob(o)
        return struct.unpack_from("<i", b, off)[0] if len(b) >= off + 4 else None

    # --- Objekt-Infos
    def name_of(self, o):
        on = self.L["name"]
        s = self.names.get(self.i32(o, on))
        n = self.i32(o, on + 4)
        if s is not None and n and n > 0:
            s = "%s_%d" % (s, n - 1)
        return s

    def class_of(self, o):
        t = self.pt(o, self.L["cls"])
        return t if t in self.set else None

    def cls_name(self, o):
        c = self.class_of(o)
        return self.name_of(c) if c else None

    def cls(self, name):
        lst = self.classes.get(name)
        return lst[0] if lst else None

    def struct(self, name):
        lst = self.structs.get(name)
        return lst[0] if lst else None

    def full_name(self, o):
        parts, n = [], 0
        while o in self.set and n < 10:
            parts.append(self.name_of(o) or "?")
            o = self.pt(o, self.L["outer"]) if self.L.get("outer") is not None else None
            n += 1
        return ".".join(reversed(parts))

    def super_of(self, c):
        s = self.pt(c, self.L.get("super"))
        return s if s in self.set else None

    def inherits(self, c, name):
        n = 0
        while c and n < 50:
            if self.name_of(c) == name:
                return True
            c, n = self.super_of(c), n + 1
        return False

    def is_a(self, o, name):
        c = self.class_of(o)
        if c is None:
            return False
        key = (c, name)
        if key not in self._isa:
            self._isa[key] = self.inherits(c, name)
        return self._isa[key]

    # --- Property-Zugriff (UObject- oder FField-Variante)
    def okp(self, p):
        return self.P.valid(p) if self.L.get("ff") else p in self.set

    def pname(self, p):
        if self.L.get("ff"):
            return self.names.get(self.i32(p, self.L.get("fname")))
        return self.name_of(p)

    def pcls_name(self, p):
        if self.L.get("ff"):
            fc = self.pt(p, self.L.get("fcls"))
            return self.names.get(self.i32(fc, 0)) if self.P.valid(fc) else None
        return self.cls_name(p)

    def owner_of(self, p):
        return self.pt(p, self.L.get("fowner" if self.L.get("ff") else "outer"))

    # --- Entdeckung: UObject-Layout
    def discover(self):
        ps = self.P.ps
        step = max(1, len(self.arr) // 1500)
        sample = [(i, self.arr[i]) for i in range(0, len(self.arr), step) if self.arr[i]]
        if len(sample) < 100:
            return False
        ptr_offs = []
        for off in range(ps, 0x80, ps):
            vals = [v for v in (self.pt(o, off) for _, o in sample) if v is not None]
            if vals and sum(v in self.set for v in vals) / len(vals) > 0.8:
                ptr_offs.append((off, vals))
        best = (0, None, None)
        for off, vals in ptr_offs:
            targets = list(set(v for v in vals if v in self.set))[:300]
            for on in range(4, 0x80, 4):
                found = set()
                for t in targets:
                    n = self.names.get(self.i32(t, on))
                    if n in KNOWN:
                        found.add(n)
                if len(found) > best[0]:
                    best = (len(found), off, on)
        if best[0] < 4:
            return False
        _, oc, on = best
        self.L.update(cls=oc, name=on)

        for off in range(0, 0x80, 4):
            hits = sum(self.i32(o, off) == i for i, o in sample)
            if hits / len(sample) > 0.9:
                self.L["index"] = off
                break

        probe = [o for _, o in sample if self.cls_name(o) in
                 ("Function", "ObjectProperty", "IntProperty", "FloatProperty",
                  "BoolProperty", "StructProperty")][:150]
        best_o = (0.0, None)
        for off, _ in ptr_offs:
            if off == oc or not probe:
                continue
            ok = 0
            for o in probe:
                t = self.pt(o, off)
                if t in self.set and self.cls_name(t) in CLASS_OK_FOR_OUTER:
                    ok += 1
            if ok / len(probe) > best_o[0]:
                best_o = (ok / len(probe), off)
        self.L["outer"] = best_o[1]
        return True

    def build_index(self):
        L, P = self.L, self.P
        need = L["cls"] + P.ps
        bycls = {}
        total = len(self.arr)
        for n, o in enumerate(self.arr):
            if not o:
                continue
            if n and n % 100000 == 0:
                log("    %d / %d" % (n, total))
            b = P.read(o, need)
            if not b or len(b) < need:
                continue
            c = struct.unpack_from(P.fmt, b, L["cls"])[0]
            if c in self.set:
                bycls.setdefault(c, []).append(o)
        for c, lst in bycls.items():
            self.inst.setdefault(self.name_of(c), []).extend(lst)
        for table, kind in ((self.classes, "Class"), (self.structs, "ScriptStruct")):
            for o in self.inst.get(kind, []):
                table.setdefault(self.name_of(o), []).append(o)
            for lst in table.values():
                if len(lst) > 1:
                    lst.sort(key=lambda o: 0 if self.full_name(o).startswith(PREFERRED_PKG) else 1)

    # --- Entdeckung: UStruct / UProperty / FProperty
    def chain(self, s):
        L = self.L
        ff = L.get("ff")
        first = L.get("cprops" if ff else "children")
        nxt = L.get("fnext" if ff else "next")
        out, seen = [], set()
        p = self.pt(s, first)
        while self.okp(p) and p not in seen and len(out) < 20000:
            seen.add(p)
            out.append(p)
            p = self.pt(p, nxt)
        return out

    def find_prop(self, cname, pname):
        c = self.cls(cname)
        for p in self.chain(c) if c else []:
            if self.pname(p) == pname:
                return p
        return None

    def discover_fprops(self, act):
        """UE4.25+: Properties sind FField-Objekte ausserhalb von GObjects."""
        L, P, ps = self.L, self.P, self.P.ps
        skip = {L.get(k) for k in ("cls", "outer", "super", "children", "next")}
        for off in range(0x20, 0x180, ps):
            if off in skip:
                continue
            p = self.pt(act, off)
            if not P.valid(p) or p in self.set or P.in_image(p):
                continue
            for fnext in range(ps, 0x48, ps):
                chain, seen, q = [], set(), p
                while P.valid(q) and q not in seen and len(chain) < 4000:
                    seen.add(q)
                    chain.append(q)
                    q = self.pt(q, fnext)
                if len(chain) < 8:
                    continue
                nodes = chain[:200]
                for fname in range(ps, 0x48, 4):
                    nm = [self.names.get(self.i32(x, fname)) for x in nodes]
                    good = sum(1 for n in nm if n and n.isidentifier())
                    if "Owner" not in nm or good < 0.9 * len(nm):
                        continue
                    # FFieldClass-Zeiger (Name endet auf "Property")
                    fcls = None
                    for o2 in range(ps, 0x40, ps):
                        if o2 == fnext:
                            continue
                        ok = 0
                        for x in nodes:
                            fc = self.pt(x, o2)
                            n = self.names.get(self.i32(fc, 0)) if P.valid(fc) else None
                            ok += bool(n and n.endswith("Property"))
                        if ok >= 0.9 * len(nodes):
                            fcls = o2
                            break
                    if fcls is None:
                        continue
                    fowner = None
                    for o2 in range(ps, 0x40, ps):
                        if o2 in (fnext, fcls):
                            continue
                        if sum(self.pt(x, o2) == act for x in nodes) >= 0.9 * len(nodes):
                            fowner = o2
                            break
                    L.update(ff=True, cprops=off, fnext=fnext, fname=fname, fcls=fcls, fowner=fowner)
                    return True
        return False

    def discover_struct(self):
        L, ps = self.L, self.P.ps
        act = self.cls("Actor")
        if not act or L.get("outer") is None:
            return False
        L["ff"] = False

        # UStruct::SuperStruct
        pairs = [("Pawn", "Actor"), ("Controller", "Actor"),
                 ("PlayerController", "Controller"), ("Actor", "Object")]
        for off in range(0x20, 0x180, ps):
            tot = ok = 0
            for c, s in pairs:
                co, so = self.cls(c), self.cls(s)
                if co and so:
                    tot += 1
                    ok += self.pt(co, off) == so
            if tot >= 2 and ok == tot:
                L["super"] = off
                break

        # UStruct::Children / UField::Next (UObject-Kette)
        for off in range(0x20, 0x180, ps):
            t = self.pt(act, off)
            if t in self.set and t != act and self.pt(t, L["outer"]) == act:
                L["children"] = off
                break
        if L.get("children") is not None:
            child = self.pt(act, L["children"])
            for off in range(0x10, 0x100, ps):
                t = self.pt(child, off)
                if t in self.set and t != child and self.pt(t, L["outer"]) == act:
                    L["next"] = off
                    if len(self.chain(act)) >= 3:
                        break
                    L["next"] = None

        # Gibt es UProperty-Objekte? Sonst FField-Modus (UE4.25+)
        props = []
        if L.get("next") is not None:
            props = [p for p in self.chain(act) if (self.cls_name(p) or "").endswith("Property")]
        if not props:
            if not self.discover_fprops(act):
                return False
            props = [p for p in self.chain(act) if (self.pcls_name(p) or "").endswith("Property")]
        if not props:
            return False

        # ArrayDim / ElementSize
        exp = expected_sizes(ps)
        named = [(p, exp[self.pname(p)]) for p in props if self.pname(p) in exp]
        es_off = None
        if named:
            for off in range(0x20, 0x180, 4):
                m = sum(self.i32(p, off) == sz and self.i32(p, off - 4) == 1 for p, sz in named)
                if m >= 3 and m >= 0.8 * len(named):
                    es_off = off
                    break
        L["esize"] = es_off

        # Offset_Internal / Offset
        def score(off):
            vals = [self.i32(p, off) for p in props]
            good = [v is not None and 0 <= v < 0x4000 for v in vals]
            if sum(good) < 0.8 * len(props):
                return -1.0
            spans, aligned, n = [], 0, 0
            for p, v, g in zip(props, vals, good):
                cn = self.pcls_name(p)
                if not g or cn == "BoolProperty":
                    continue  # Bools teilen sich Bitfeld-Bytes
                size, dim = self.i32(p, es_off), self.i32(p, es_off - 4)
                if not size or not dim or size <= 0 or dim <= 0:
                    continue
                spans.append((v, v + size * dim))
                n += 1
                al = ps if cn in ("ObjectProperty", "ClassProperty", "ArrayProperty",
                                  "InterfaceProperty", "WeakObjectProperty", "SoftObjectProperty",
                                  "ObjectPtrProperty", "MapProperty", "SetProperty") else 4
                if cn in ("ByteProperty",):
                    al = 1
                aligned += v % al == 0
            if n < 10:
                return -1.0
            spans.sort()
            ok = sum(spans[i][1] <= spans[i + 1][0] for i in range(len(spans) - 1))
            return ok / max(1, len(spans) - 1) + aligned / n

        if es_off is not None:
            scores = sorted(((score(off), off) for off in range(0x20, 0x180, 4)
                             if off not in (L.get("index"), es_off, es_off - 4)), reverse=True)
            log("[dbg] Property-Offset Kandidaten (Score, Offset): " +
                ", ".join("%.2f@0x%X" % s for s in scores[:5]) +
                "  (%d Properties in Actor, %s)" % (len(props), "FField" if L["ff"] else "UProperty"))
            if scores and scores[0][0] >= 1.5:
                L["poff"] = scores[0][1]

        # PropertyClass / Struct / Inner
        skip = {L.get(k) for k in ("cls", "outer", "next", "super", "fnext", "fcls", "fowner", "poff")}
        skip |= {es_off, (es_off - 4) if es_off else None}
        own = self.find_prop("Actor", "Owner")
        pawn_ctrl = self.find_prop("Pawn", "Controller")
        cc = self.cls("Controller")
        if own:
            for off in range(0x20, 0x180, ps):
                if off in skip:
                    continue
                if self.pt(own, off) == act and (not pawn_ctrl or self.pt(pawn_ctrl, off) == cc):
                    L["pcls"] = off
                    break
        sprops = [p for p in props if self.pcls_name(p) == "StructProperty"][:6]
        if sprops:
            for off in range(0x20, 0x180, ps):
                if off in skip:
                    continue
                if all(self.pt(p, off) in self.set and
                       self.cls_name(self.pt(p, off)) == "ScriptStruct" for p in sprops):
                    L["struct"] = off
                    break
        arr = next((p for p in props if self.pcls_name(p) == "ArrayProperty"), None)
        if arr:
            for off in range(0x20, 0x180, ps):
                if off in skip:
                    continue
                t = self.pt(arr, off)
                if t and t != arr and self.okp(t) and self.owner_of(t) == arr:
                    L["inner"] = off
                    break
        L["ssize"] = self.find_ssize()
        return all(L.get(k) is not None for k in ("super", "poff")) and \
            (L.get("children") is not None or L.get("ff"))

    def find_ssize(self):
        """UStruct::PropertiesSize - aus bekannten Struct-Groessen (Guid, Color, Vector ...)."""
        pres = [(self.struct(n), vals) for n, vals in STRUCT_SIZES.items() if self.struct(n)]
        if len(pres) < 3:
            return None
        L = self.L
        skip = {L.get(k) for k in ("cls", "outer", "next", "super", "children", "name", "index")}
        for off in range(0x20, 0x180, 4):
            if off in skip:
                continue
            if all(self.i32(s, off) in vals for s, vals in pres):
                return off
        return None

    # --- Member
    def describe(self, p, depth=0):
        L = self.L
        cn = self.pcls_name(p)
        d = {"name": self.pname(p), "type": cn, "offset": self.i32(p, L.get("poff")),
             "size": self.i32(p, L.get("esize")), "label": (cn or "?").replace("Property", "")}
        if cn == "StructProperty":
            t = self.pt(p, L.get("struct"))
            if t in self.set:
                d["_struct"], d["label"] = t, self.name_of(t)
        elif cn in OBJECT_PROP_TYPES:
            t = self.pt(p, L.get("pcls"))
            if t in self.set:
                d["label"] = (self.name_of(t) or "?") + "*"
        elif cn == "ArrayProperty" and depth < 2:
            t = self.pt(p, L.get("inner"))
            if t and self.okp(t):
                inner = self.describe(t, depth + 1)
                d["label"] = "TArray<%s>" % inner["label"]
                if inner.get("_struct"):
                    d["_struct"] = inner["_struct"]
        return d

    def members(self, s):
        if s not in self._members:
            ms = [self.describe(p) for p in self.chain(s)
                  if (self.pcls_name(p) or "").endswith("Property")]
            ms.sort(key=lambda d: d["offset"] or 0)
            self._members[s] = ms
        return self._members[s]

    def find_member(self, cname, members):
        for m in members:
            c, n = self.cls(cname), 0
            while c and n < 50:
                for d in self.members(c):
                    if d["name"] == m:
                        return dict(d, owner=self.name_of(c))
                c, n = self.super_of(c), n + 1
        return None

    def tree(self, d, depth, lines, indent="  "):
        off = d["offset"]
        lines.append("%s+0x%03X  %-22s %s%s" % (
            indent, off if off is not None else 0, d["label"], d["name"],
            "   (von %s)" % d["owner"] if d.get("owner") else ""))
        if d.get("_struct") and depth > 0:
            for m in self.members(d["_struct"]):
                self.tree(m, depth - 1, lines, indent + "    ")

    def find_ptrs_to_class(self, obj, cname, span=0x400):
        b = self.P.read(obj, span) or b""
        ps, out = self.P.ps, []
        for off in range(0, len(b) - ps + 1, ps):
            v = struct.unpack_from(self.P.fmt, b, off)[0]
            if v in self.set and self.cls_name(v) == cname:
                out.append((off, v))
        return out

    def find_actor_arrays(self, level, span=0x600):
        P, ps = self.P, self.P.ps
        b = P.read(level, span) or b""
        res = []
        for off in range(0, len(b) - ps - 8, ps):
            data = struct.unpack_from(P.fmt, b, off)[0]
            num, mx = struct.unpack_from("<ii", b, off + ps)
            if not (P.valid(data) and 0 < num < 500000 and mx >= num):
                continue
            head = P.read(data, min(num, 64) * ps)
            if not head:
                continue
            vals = struct.unpack("<%d%s" % (len(head) // ps, P.ch), head)
            nn = [v for v in vals if v in self.set]
            hits = sum(self.is_a(v, "Actor") for v in nn)
            if hits >= 5 and hits >= 0.3 * len(vals):
                res.append((num, off))
        return sorted(res, reverse=True)


# ----------------------------------------------------------------------------
# GObjects finden
# ----------------------------------------------------------------------------
def plausible_obj(P, o):
    return P.valid(o) and P.in_image(P.ptr(o))  # erstes Wort = vtable im Image


def probe_items(P, addr, stride, n=8):
    b = P.read(addr, n * stride)
    if not b or len(b) < n * stride:
        return False
    ok = 0
    for i in range(n):
        o = struct.unpack_from(P.fmt, b, i * stride)[0]
        if o:
            if not plausible_obj(P, o):
                return False
            ok += 1
    return ok >= 5


def read_items(P, addr, stride, count):
    raw = P.read_big(addr, count * stride)
    return [struct.unpack_from(P.fmt, raw, i * stride)[0] for i in range(count)]


def find_gobjects(P, names):
    ps = P.ps
    tried = set()

    # A) TArray<UObject*>  (UE1-3, UE4 < 4.11)
    for indirect in (False, True):
        for addr, data, num in tarray_candidates(P, 5000, 10_000_000, indirect):
            if addr in tried:
                continue
            tried.add(addr)
            head = P.read(data, 64 * ps)
            if not head or len(head) < 64 * ps:
                continue
            vals = struct.unpack("<64%s" % P.ch, head)
            nn = [v for v in vals if v]
            if len(nn) < 32 or not all(P.valid(v) for v in nn) or not plausible_obj(P, nn[0]):
                continue
            arr = struct.unpack("<%d%s" % (num, P.ch), P.read_big(data, num * ps))
            objs = Objects(P, names, arr)
            if objs.discover():
                return {"mode": "TArray<UObject*>", "rva": hex(addr - P.base),
                        "deref": indirect, "count": num}, objs

    # B) FUObjectItem-Arrays (UE4.11+ / UE5): chunked oder flach
    for addr, v, w1, w2 in P.ptrs:
        if P.in_image(v):
            continue
        # B1) chunked: {Item** Objects; Item* PreAlloc; int Max; int Num; int MaxChunks; int NumChunks}
        if ps == 8:
            mx, num = w2 & 0xFFFFFFFF, w2 >> 32
            pre_ok = 5000 < num < 10_000_000 and mx >= num
        else:
            mx, num, pre_ok = w2, 0, 5000 < w2 < 10_000_000
        if pre_ok:
            c0 = P.ptr(v)
            if P.valid(c0) and not P.in_image(c0):
                for stride in (0x18, 0x10, 0x20):
                    if not probe_items(P, c0, stride):
                        continue
                    hdr = P.read(addr, 6 * ps if ps == 4 else 0x20)
                    if not hdr:
                        continue
                    mx, num, mch, nch = struct.unpack_from("<4i", hdr, 2 * ps)
                    if not (5000 < num < 10_000_000 and mx >= num and nch == (num + 65535) // 65536):
                        continue
                    arr = []
                    for ci in range(nch):
                        ch = P.ptr(v + ci * ps)
                        if not P.valid(ch):
                            break
                        arr += read_items(P, ch, stride, min(65536, num - ci * 65536))
                    objs = Objects(P, names, arr)
                    if objs.discover():
                        return {"mode": "FUObjectItem chunked", "rva": hex(addr - P.base),
                                "FUObjectArray_rva_guess": hex(addr - P.base - 0x10),
                                "item_size": hex(stride), "count": num}, objs
        # B2) flach: {Item* Objects; int Max; int Num}
        if ps == 8:
            mx, num = w1 & 0xFFFFFFFF, w1 >> 32
        else:
            mx, num = w1, w2
        if 5000 < num < 10_000_000 and mx >= num:
            for stride in (0x18, 0x10, 0x20):
                if not probe_items(P, v, stride):
                    continue
                arr = read_items(P, v, stride, num)
                objs = Objects(P, names, arr)
                if objs.discover():
                    return {"mode": "FUObjectItem flat", "rva": hex(addr - P.base),
                            "FUObjectArray_rva_guess": hex(addr - P.base - 0x10),
                            "item_size": hex(stride), "count": num}, objs
    return None


# ----------------------------------------------------------------------------
# Hilfen
# ----------------------------------------------------------------------------
def guess_engine(names, objs):
    L = objs.L
    if names.mode == "FNamePool":
        v = "UE4.23+ / UE5"
    elif names.mode.startswith("TNameEntryArray"):
        v = "UE4.11 - 4.22"
    else:
        v = "UE1-3 / UE4 < 4.11"
    if L.get("ff"):
        v = "UE4.25+ / UE5 (FProperty)"
    vec = objs.struct("Vector")
    if vec and L.get("ssize") is not None and objs.i32(vec, L["ssize"]) == 24:
        v = "UE5 (Large World Coordinates, double-Vector)"
    return v


def pick_process():
    """Zeigt alle Prozesse; Eingabe = Nummer, kompletter Name oder Teilname (z.B. 'outlast')."""
    allp = set()
    try:
        for p in pymem.process.list_processes():
            allp.add(p.szExeFile.decode(errors="ignore"))
    except Exception:
        pass
    allp = sorted(allp, key=str.lower)
    likely = [n for n in allp if re.search(r"(shipping|win64|win32|udk|ue[345]|game|outlast|olgame)", n, re.I)]
    log("Wahrscheinliche Spielprozesse:" if likely else "Alle Prozesse:")
    shown = likely or allp
    for i, n in enumerate(shown):
        log("  [%d] %s" % (i, n))
    while True:
        s = input("Nummer, Name oder Teilname (a = alle anzeigen): ").strip()
        if s.lower() == "a":
            shown = allp
            for i, n in enumerate(shown):
                log("  [%d] %s" % (i, n))
            continue
        if s.isdigit() and int(s) < len(shown):
            return shown[int(s)]
        hits = [n for n in allp if s.lower() in n.lower()]
        if len(hits) == 1:
            return hits[0]
        if hits:
            log("Mehrere Treffer: " + ", ".join(hits))
            continue
        if s:
            return s  # exakter Name unbekannt -> pymem versuchen lassen


# ----------------------------------------------------------------------------
# Hauptprogramm
# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Universal Unreal Engine Dumper (UE3/UE4/UE5)")
    ap.add_argument("--exe", help="Prozessname, z.B. Game-Win64-Shipping.exe")
    ap.add_argument("--pid", type=int, help="alternativ: Prozess-ID")
    ap.add_argument("--names", action="store_true", help="names.txt schreiben")
    ap.add_argument("--objects", action="store_true", help="objects.txt schreiben (langsam)")
    ap.add_argument("--sdk", action="store_true", help="sdk_dump.txt (Klassen + Structs) schreiben")
    ap.add_argument("--class", dest="cls", nargs="+", default=[], metavar="NAME",
                    help="Member dieser Klassen(inkl. Vererbung) ausgeben")
    ap.add_argument("--out", default="ue_offsets.json")
    args = ap.parse_args()

    if not args.exe and not args.pid:
        args.exe = pick_process()
    try:
        P = Proc(args.exe, args.pid)
    except Exception as e:
        sys.exit("Prozess nicht gefunden (%s). Spiel gestartet? Als Admin ausfuehren?" % e)
    log("[+] %s: Base=0x%X, Image=0x%X, %d-Bit" % (P.exe, P.base, P.size, P.ps * 8))
    result = {"exe": P.exe, "bits": P.ps * 8}

    log("[*] Lese beschreibbare Sektionen ...")
    P.load()
    log("    %d Zeiger-Woerter" % len(P.ptrs))

    # --- GNames
    log("[*] Suche GNames (FNamePool / chunked / TArray) ...")
    names = find_names(P)
    if not names:
        sys.exit("[-] GNames nicht gefunden. Laeuft ein Level? Schutz/Packer aktiv?")
    result["GNames"] = names.info(P)
    log("[+] GNames: %s" % json.dumps(result["GNames"]))

    # --- GObjects
    log("[*] Suche GObjects (kann einige Sekunden dauern) ...")
    g = find_gobjects(P, names)
    if not g:
        sys.exit("[-] GObjects nicht gefunden.")
    desc, objs = g
    result["GObjects"] = desc
    log("[+] GObjects: %s" % json.dumps(desc))

    log("[*] Indiziere %d Objekte ..." % objs.num)
    objs.build_index()
    ok = objs.discover_struct()
    L = objs.L
    result["UObject"] = {k: hex(L[k]) for k in ("index", "outer", "name", "cls") if L.get(k) is not None}
    result["UStruct_UProperty"] = {k: hex(L[k]) for k in
                                   ("super", "children", "next", "cprops", "fnext", "fname", "fcls",
                                    "fowner", "poff", "esize", "struct", "pcls", "inner", "ssize")
                                   if L.get(k) is not None}
    result["UStruct_UProperty"]["property_model"] = "FField (UE4.25+)" if L.get("ff") else "UProperty-UObject"
    result["Engine"] = guess_engine(names, objs)
    log("[+] UObject: " + ", ".join("%s=0x%X" % (k, v) for k, v in L.items()
                                    if isinstance(v, int) and not isinstance(v, bool)))
    log("[+] Engine-Schaetzung: %s" % result["Engine"])
    if not ok:
        log("[!] UStruct/UProperty-Layout unvollstaendig - Member-Dump evtl. nicht moeglich.")

    # --- GWorld / GEngine
    def live(o):
        return not (objs.name_of(o) or "").startswith("Default__")

    worlds = [o for o in objs.inst.get("World", []) if live(o)]
    engines = []
    for cn in list(objs.inst):
        c = objs.cls(cn)
        if c and objs.inherits(c, "Engine"):
            engines += [(cn, e) for e in objs.inst[cn] if live(e)]
    refs = P.refs_to(set(worlds) | {e for _, e in engines})
    result["GWorld"], result["GEngine"] = [], []
    for w in worlds:
        for rva in refs.get(w, []):
            result["GWorld"].append(hex(rva))
            log("[+] GWorld  = %s+0x%X  (%s)" % (P.exe, rva, objs.name_of(w)))
    if not result["GWorld"]:
        log("[-] Kein globaler Zeiger auf die World-Instanz gefunden.")
    for cn, e in engines:
        for rva in refs.get(e, []):
            result["GEngine"].append(hex(rva))
            log("[+] GEngine = %s+0x%X  (%s)" % (P.exe, rva, cn))

    # --- Level / Actor-Array
    result["Level"] = {}
    for w in worlds:
        lv = objs.find_ptrs_to_class(w, "Level")
        if not lv:
            continue
        lv.sort(key=lambda x: objs.name_of(x[1]) != "PersistentLevel")
        pl_off, level = lv[0]
        arrs = objs.find_actor_arrays(level)
        result["Level"] = {"World.PersistentLevel": hex(pl_off)}
        log("[+] World.PersistentLevel = +0x%X" % pl_off)
        for num, off in arrs[:3]:
            log("[+] Level.Actors (TArray) = +0x%X  (Count @ +0x%X, aktuell %d)" % (off, off + P.ps, num))
        if arrs:
            result["Level"].update({"Actors": hex(arrs[0][1]), "ActorCount": hex(arrs[0][1] + P.ps)})
        break

    # --- Wichtige Member
    result["Members"] = {}
    if ok:
        log("\n=== Wichtige Member (relativ zum jeweiligen Objekt/Struct) ===")
        for classes, members in KEY_MEMBERS:
            d = None
            for c in classes:
                d = objs.find_member(c, members)
                if d:
                    break
            if not d:
                log("  [-] %s.%s nicht gefunden" % (classes[0], members[0]))
                continue
            lines = []
            objs.tree(d, 3, lines)
            log("\n".join(lines))
            result["Members"]["%s.%s" % (d["owner"], d["name"])] = hex(d["offset"] or 0)

    # --- Pawn-Unterklassen (Kandidaten)
    log("\n=== Pawn-Unterklassen mit lebenden Instanzen ===")
    cand = {}
    for cn, lst in objs.inst.items():
        if cn in ("Class",) or not objs.cls(cn):
            continue
        n = sum(1 for o in lst if live(o))
        if n and objs.inherits(objs.cls(cn), "Pawn"):
            cand[cn] = n
    for cn, n in sorted(cand.items()):
        log("  %-40s %d" % (cn, n))
    result["PawnClasses"] = cand

    # --- Einzelne Klassen ausgeben
    if ok:
        for cn in args.cls:
            c = objs.cls(cn) or objs.struct(cn)
            if not c:
                log("[-] Klasse/Struct %s nicht gefunden" % cn)
                continue
            chain, n = [], 0
            while c and n < 50:
                chain.append(c)
                c, n = objs.super_of(c), n + 1
            for c in reversed(chain):
                sz = objs.i32(c, L.get("ssize"))
                log("\nclass %s  (size=0x%X)" % (objs.full_name(c), sz or 0))
                for d in objs.members(c):
                    log("  +0x%03X  %-26s %s" % (d["offset"] or 0, d["label"], d["name"]))

    # --- Optional-Dumps
    if args.names:
        with open("names.txt", "w", encoding="utf-8") as f:
            for i, s in names.items():
                f.write("%d\t%s\n" % (i, s))
        log("[+] names.txt geschrieben")
    if args.objects:
        log("[*] Schreibe objects.txt (kann dauern) ...")
        with open("objects.txt", "w", encoding="utf-8") as f:
            for i, o in enumerate(objs.arr):
                if o:
                    f.write("%d\t0x%X\t%s\t%s\n" % (i, o, objs.cls_name(o), objs.full_name(o)))
        log("[+] objects.txt geschrieben")
    if args.sdk and ok:
        with open("sdk_dump.txt", "w", encoding="utf-8") as f:
            for kind, table in (("class", objs.classes), ("struct", objs.structs)):
                for cn in sorted(table, key=lambda x: x or ""):
                    for c in table[cn]:
                        sup = objs.super_of(c)
                        sz = objs.i32(c, L.get("ssize"))
                        f.write("%s %s : %s  // size=0x%X\n" % (
                            kind, objs.full_name(c), objs.name_of(sup) if sup else "-", sz or 0))
                        for d in objs.members(c):
                            f.write("  +0x%03X  %-26s %s\n" % (d["offset"] or 0, d["label"], d["name"]))
                        f.write("\n")
        log("[+] sdk_dump.txt geschrieben")

    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
    log("\n[+] Fertig -> %s" % args.out)
    log("Typische Zeigerketten:")
    log("  UE3 : GEngine -> GamePlayers[0] -> Player.Actor -> PlayerCamera -> CameraCache.POV")
    log("  UE4+: GEngine -> GameInstance -> LocalPlayers[0] -> PlayerController -> PlayerCameraManager")
    log("        GWorld  -> PersistentLevel -> Actors[i] -> RootComponent -> RelativeLocation")


if __name__ == "__main__":
    main()
