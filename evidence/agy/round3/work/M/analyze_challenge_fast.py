import json, time

path = "~/rh-audit/export/challenge.ndjson"
t0 = time.time()

names = {0: ""}
name_raw = {}
axioms = []
target_decls = []
rh_nids = set()
RH_nids = set()

# Pass 1: collect all name records, all axiom records, and decls for riemannHypothesis / RiemannHypothesis
with open(path, "rb") as f:
    for lineno, line in enumerate(f, 1):
        if b'"in":' in line:
            obj = json.loads(line)
            if "in" in obj:
                nid = obj["in"]
                if "str" in obj:
                    p = obj["str"]["pre"]
                    s = obj["str"]["str"]
                    pre = names.get(p, f"<{p}>")
                    full = f"{pre}.{s}" if pre else s
                    names[nid] = full
                    if s in ("riemannHypothesis", "RiemannHypothesis"):
                        name_raw[nid] = (lineno, line.decode().strip())
                        if s == "riemannHypothesis":
                            rh_nids.add(nid)
                        else:
                            RH_nids.add(nid)
                elif "num" in obj:
                    p = obj["num"]["pre"]
                    i = obj["num"]["i"]
                    pre = names.get(p, f"<{p}>")
                    names[nid] = f"{pre}.{i}" if pre else str(i)
        elif b'"axiom":' in line:
            obj = json.loads(line)
            if "axiom" in obj:
                ax = obj["axiom"]
                axioms.append((lineno, ax["name"], names.get(ax["name"]), ax["type"], line.decode().strip()))
        elif b'"thm":' in line or b'"def":' in line or b'"opaque":' in line:
            if rh_nids or RH_nids:
                # cheap check before json.loads
                for nid in rh_nids | RH_nids:
                    if f'"name":{nid},'.encode() in line or f'"name":{nid}}}'.encode() in line:
                        obj = json.loads(line)
                        for k in ("thm", "def", "opaque"):
                            if k in obj and obj[k]["name"] == nid:
                                target_decls.append((lineno, k, nid, names.get(nid), obj[k], line.decode().strip()))

print(f"Pass 1 done in {time.time()-t0:.2f}s (total lines: {lineno})")
print("\n=== riemannHypothesis name records ===")
for nid in sorted(rh_nids):
    print(f"nid={nid} full={names[nid]} L{name_raw[nid][0]}: {name_raw[nid][1]}")

print("\n=== RiemannHypothesis name records ===")
for nid in sorted(RH_nids):
    print(f"nid={nid} full={names[nid]} L{name_raw[nid][0]}: {name_raw[nid][1]}")

print("\n=== Target decls (thm/def/opaque) ===")
for d in target_decls:
    print(f"L{d[0]} {d[1]} nid={d[2]} ({d[3]}): {d[5]}")

print(f"\n=== ALL AXIOM RECORDS ({len(axioms)}) ===")
for a in axioms:
    print(f"L{a[0]}: nid={a[1]} name={a[2]} type_ie={a[3]} | {a[4]}")

# Pass 2: resolve the exact expression records for all axioms' types, plus target_decls' types & values
want_eids = {a[3] for a in axioms}
for d in target_decls:
    want_eids.add(d[4]["type"])
    if "value" in d[4]:
        want_eids.add(d[4]["value"])

needles = {eid: (f'"ie":{eid}}}'.encode(), f'"ie":{eid},'.encode()) for eid in want_eids}
found_exprs = {}

with open(path, "rb") as f:
    for lineno, line in enumerate(f, 1):
        if b'"ie":' in line:
            for eid, (n1, n2) in needles.items():
                if n1 in line or n2 in line:
                    obj = json.loads(line)
                    if obj.get("ie") == eid:
                        found_exprs[eid] = (lineno, line.decode().strip(), obj)
                        break

print(f"\nPass 2 done in {time.time()-t0:.2f}s")
print("\n=== Expression records for axioms & target decls ===")
for eid in sorted(want_eids):
    if eid in found_exprs:
        ln, raw, obj = found_exprs[eid]
        extra = ""
        if "const" in obj:
            cid = obj["const"]["name"]
            extra = f"  ==> const {names.get(cid)} (nid={cid}, us={obj['const']['us']})"
        elif "forallE" in obj:
            fe = obj["forallE"]
            extra = f"  ==> forallE binder={names.get(fe['name'])} type_ie={fe['type']} body_ie={fe['body']} info={fe['binderInfo']}"
        print(f"ie={eid} (L{ln}): {raw}{extra}")
    else:
        print(f"ie={eid}: NOT FOUND")
