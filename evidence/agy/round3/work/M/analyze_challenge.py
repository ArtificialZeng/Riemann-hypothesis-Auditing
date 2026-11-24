import json
import sys

path = "~/rh-audit/export/challenge.ndjson"

names = {0: ""}
name_lines = {}
axioms = []
rh_name_ids = []
RH_name_ids = []
decls_of_interest = []

# First pass: collect all names, axioms, and declarations matching riemannHypothesis or RiemannHypothesis
with open(path, "rb") as f:
    for lineno, line in enumerate(f, 1):
        if b'"in":' in line:
            obj = json.loads(line)
            if "in" in obj:
                nid = obj["in"]
                if "str" in obj:
                    p = obj["str"]["pre"]
                    pre = names.get(p, f"<{p}>")
                    s = obj["str"]["str"]
                    full = f"{pre}.{s}" if pre else s
                    names[nid] = full
                    if s in ("riemannHypothesis", "RiemannHypothesis", "sorryAx", "propext", "Quot.sound", "sound", "choice"):
                        name_lines[nid] = (lineno, line.decode().strip())
                    if s == "riemannHypothesis":
                        rh_name_ids.append((lineno, nid, full, line.decode().strip()))
                    if s == "RiemannHypothesis":
                        RH_name_ids.append((lineno, nid, full, line.decode().strip()))
                elif "num" in obj:
                    p = obj["num"]["pre"]
                    pre = names.get(p, f"<{p}>")
                    i = obj["num"]["i"]
                    full = f"{pre}.{i}" if pre else str(i)
                    names[nid] = full
        elif b'"axiom":' in line:
            obj = json.loads(line)
            if "axiom" in obj:
                ax = obj["axiom"]
                axioms.append((lineno, ax["name"], names.get(ax["name"]), ax["type"], line.decode().strip()))
        elif b'"thm":' in line or b'"def":' in line:
            # quick filter for our target name ids once found
            if rh_name_ids or RH_name_ids:
                obj = json.loads(line)
                for k in ("thm", "def"):
                    if k in obj:
                        nid = obj[k]["name"]
                        if any(nid == x[1] for x in rh_name_ids) or any(nid == x[1] for x in RH_name_ids):
                            decls_of_interest.append((lineno, k, nid, names.get(nid), obj[k], line.decode().strip()))

print("=== riemannHypothesis name records ===")
for x in rh_name_ids:
    print(x)

print("\n=== RiemannHypothesis name records ===")
for x in RH_name_ids:
    print(x)

print("\n=== Decls of interest (thm/def) ===")
for x in decls_of_interest:
    print(x[:4], x[5])

print(f"\n=== ALL AXIOM RECORDS ({len(axioms)}) ===")
for a in axioms:
    print(f"line {a[0]}: name_id={a[1]} ({a[2]}), type_id={a[3]} | {a[4]}")

# Collect expression ids we want to inspect
want_eids = set()
for a in axioms:
    want_eids.add(a[3])
for d in decls_of_interest:
    want_eids.add(d[4]["type"])
    if "value" in d[4]:
        want_eids.add(d[4]["value"])

# Second pass: collect needed exprs (and recursively resolve if small, or grab all exprs referenced by RiemannHypothesis / riemannHypothesis)
# Better yet, find the max eid we care about? Wait, just resolve direct exprs first, plus full tree of riemannHypothesis type & RiemannHypothesis def!
expr_lines = {}
all_exprs = {}
with open(path, "rb") as f:
    for lineno, line in enumerate(f, 1):
        if b'"ie":' in line:
            obj = json.loads(line)
            if "ie" in obj:
                ie = obj["ie"]
                if ie in want_eids:
                    expr_lines[ie] = (lineno, line.decode().strip(), obj)
                all_exprs[ie] = (lineno, obj)

print("\n=== Direct expression records for want_eids ===")
for eid in sorted(want_eids):
    if eid in expr_lines:
        lineno, raw, obj = expr_lines[eid]
        print(f"ie={eid} (line {lineno}): {raw}")
        if "const" in obj:
            cname_id = obj["const"]["name"]
            print(f"   -> const name_id={cname_id} => {names.get(cname_id)}")

def dump_expr(eid, depth=0, max_depth=8, seen=None):
    if seen is None:
        seen = set()
    indent = "  " * depth
    if eid not in all_exprs:
        return f"{indent}<missing ie={eid}>"
    lineno, obj = all_exprs[eid]
    if depth > max_depth:
        return f"{indent}ie={eid} (line {lineno}) ..."
    if "const" in obj:
        cid = obj["const"]["name"]
        return f"{indent}ie={eid} (L{lineno}): const {names.get(cid)} (name_id={cid}, us={obj['const']['us']})"
    if "sort" in obj:
        return f"{indent}ie={eid} (L{lineno}): sort {obj['sort']}"
    if "bvar" in obj:
        return f"{indent}ie={eid} (L{lineno}): bvar {obj['bvar']}"
    if "natVal" in obj:
        return f"{indent}ie={eid} (L{lineno}): natVal {obj['natVal']}"
    if "strVal" in obj:
        return f"{indent}ie={eid} (L{lineno}): strVal {obj['strVal']}"
    if "forallE" in obj:
        fe = obj["forallE"]
        n = names.get(fe["name"], str(fe["name"]))
        return (f"{indent}ie={eid} (L{lineno}): forallE ({n} : [type={fe['type']}] [{fe['binderInfo']}]) -> [body={fe['body']}]\n"
                + dump_expr(fe["type"], depth+1, max_depth) + "\n"
                + dump_expr(fe["body"], depth+1, max_depth))
    if "lam" in obj:
        lm = obj["lam"]
        n = names.get(lm["name"], str(lm["name"]))
        return (f"{indent}ie={eid} (L{lineno}): lam ({n} : [type={lm['type']}]) => [body={lm['body']}]\n"
                + dump_expr(lm["type"], depth+1, max_depth) + "\n"
                + dump_expr(lm["body"], depth+1, max_depth))
    if "app" in obj:
        ap = obj["app"]
        return (f"{indent}ie={eid} (L{lineno}): app (fn={ap['fn']}, arg={ap['arg']})\n"
                + dump_expr(ap["fn"], depth+1, max_depth) + "\n"
                + dump_expr(ap["arg"], depth+1, max_depth))
    return f"{indent}ie={eid} (L{lineno}): {obj}"

print("\n=== Unfolded expressions for decls_of_interest ===")
for d in decls_of_interest:
    print(f"\n--- {d[1]} {d[3]} (name_id={d[2]}) ---")
    print("TYPE:")
    print(dump_expr(d[4]["type"], max_depth=6))
    if "value" in d[4]:
        print("VALUE:")
        print(dump_expr(d[4]["value"], max_depth=6))

print("\n=== Unfolded types for axioms ===")
for a in axioms:
    print(f"\n--- axiom {a[2]} (name_id={a[1]}) ---")
    print(dump_expr(a[3], max_depth=4))
