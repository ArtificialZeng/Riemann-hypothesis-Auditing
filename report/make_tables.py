#!/usr/bin/env python3
"""Generate LaTeX table bodies from the conescan TSV outputs (no hand transcription)."""
import sys, os, csv
scan1, scan2, out = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)
def rows(p):
    with open(p, encoding="utf-8") as f:
        return list(csv.DictReader(f, delimiter="\t"))
def path(s): return "\\path{%s}" % s if s != "-" else "---"
def emit(src, dst, skip_self=None):
    rs = rows(src)
    with open(dst, "w", encoding="utf-8") as g:
        for i, r in enumerate(rs, 1):
            g.write("%d & %s & %s & %s & %s & %s \\\\\n" % (
                i, r["kind"], "是" if r["in_type"] == "1" else "否", "是" if r["in_value"] == "1" else "否",
                path(r["name"]), path(r["direct_witness"])))
    return len(rs)
n0 = emit(os.path.join(scan1, "tainted_bit0_anyGeometry.tsv"), os.path.join(out, "tainted_anygeometry.tex"))
n3 = emit(os.path.join(scan1, "tainted_bit3_OAt_geo_proj_.tsv"), os.path.join(out, "tainted_oatgeo.tex"))
n2 = emit(os.path.join(scan1, "tainted_bit2_GeoCl_rec_elim_.tsv"), os.path.join(out, "tainted_geoclrec.tex"))
print("anyGeometry:", n0, "OAt.geo:", n3, "GeoCl.rec:", n2)
# scan2 summary counts
import re
rep = open(os.path.join(scan2, "conescan_report.txt"), encoding="utf-8").read()
with open(os.path.join(out, "scan2_counts.tex"), "w", encoding="utf-8") as g:
    for m in re.finditer(r"SEED bit (\d+) \[(.+?)\] matched names: \[(.*?)\]\nSEED bit \d+ \[.+?\]: (\d+) declarations", rep):
        bit, lab, names, cnt = m.groups()
        names = names.replace('"', '').replace("PROJ ", "proj: ")
        dep = re.search(r"CHAIN\[%s\] riemannHypothesis: NOT dependent" % re.escape(lab), rep) is None and int(cnt) > 0
        g.write("%s & %s & %s & %s \\\\\n" % (path(lab), path(names) if names else "（名字未进入导出）", cnt, "是" if dep else "否"))
        print(lab, names, cnt, dep)
