"""Check the published evidence offline with the Python standard library."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT/"formalization/OddPiPowers"
EVIDENCE = ROOT/"evidence"
FAMILY = "OddPiPowers.PolynomialValues."
PUBLIC = FAMILY+"PolynomialEndpointsAudit"
REPORT = PROJECT/"logs/polynomial-values-acceptance-20261119.json"
SERIAL = EVIDENCE/"serial-checks.json"
OLD = PROJECT/"logs/p6-guarded-library-build-state.json"
ARCHIVE = EVIDENCE/"accepted-polynomial-oleans.zip"
STANDARD = {"propext","Classical.choice","Quot.sound"}
SIGNATURES = {
    "PiPolynomialValues.pi_quadratic_endpoint":"Endpoint Real.pi 2 (16161227/1000000)",
    "PiPolynomialValues.pi_cubic_endpoint":"Endpoint Real.pi 3 (3426527/125000)",
    "PiPolynomialValues.pi_quadratic_omega_le":"omega Real.pi 2≤((16161227/1000000 : ℝ) : EReal)",
    "PiPolynomialValues.pi_cubic_omega_le":"omega Real.pi 3≤((3426527/125000 : ℝ) : EReal)",
}
IMPORTS = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\n]+)",re.M)
LOCAL = re.compile(r"\bOddPiPowers(?:\.[A-Za-z_][A-Za-z_0-9]*)*\b")


def check(value,message):
    if not value:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def source(name):
    return PROJECT/(name.replace(".","/")+".lean")


def local_imports(name):
    raw=source(name).read_text(encoding="utf-8")
    return list(dict.fromkeys(dep for line in IMPORTS.findall(raw)
                         for dep in LOCAL.findall(line.split("--",1)[0])))


def source_order(root=PUBLIC):
    done=set()
    visiting=set()
    order=[]
    def visit(name):
        if name in done:
            return
        check(name not in visiting,"Cyclic import at "+name)
        visiting.add(name)
        for dep in local_imports(name):
            visit(dep)
        visiting.remove(name)
        done.add(name)
        order.append(name)
    visit(root)
    return order


def check_axioms(text):
    entries=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]",text)
    check([name for name,_ in entries]==list(SIGNATURES),"Unexpected audited declarations or order")
    for name,axioms in entries:
        check({s.strip() for s in axioms.split(",")}==STANDARD,"Axiom mismatch at "+name)


def main():
    check(digest(REPORT)=="d3117c2cbaec3ecbe38191f3e9658c83b63d5f1bcc1ab2c45e30807afa377070","Original acceptance report")
    check(digest(SERIAL)=="1b2d31c8ec741b7b8eaff5803ddbf276dcd9907afa07fe7a6eb15664e734179e","Serial evidence inventory")
    check(digest(OLD)=="6dd0e58b3d30113b58b188fe02f97b5ed6b5dbdb7f2e44c506693de41b7aa45b","Prior source ledger")
    report=json.loads(REPORT.read_bytes())
    rows=json.loads(SERIAL.read_bytes())["modules"]
    check(len(rows)==725,"Expected 725 successful queue entries")
    check(report["public_signatures"]==SIGNATURES,"Reported declaration types")
    check(all(set(a)==STANDARD for a in report["public_declarations"].values())
          and set(report["public_declarations"])==set(SIGNATURES),"Reported public axioms")
    check((PROJECT/"lean-toolchain").read_text().strip()==report["toolchain"]=="leanprover/lean4:v4.35.0","Toolchain")
    check(digest(PROJECT/"lake-manifest.json")==report["manifest_sha256"],"Pinned dependency manifest")
    check(digest(ROOT/"scripts/bounded_lean.py")==report["compiler_guard_sha256"],"Compilation guard")
    wrapper=ROOT/"research/pi_low_degree_lean_prep_2026-11-19/check_module.py"
    check(digest(wrapper)==report["bounded_trials"]["pinned_package_wrapper_sha256"],"Package selection wrapper")
    check(digest(PROJECT/"lakefile.toml")=="e2adc9ed44d6bff45f8ffa00408d41ebeb984e47c4e7ab5b6da9b5b39235842b","Lake configuration")

    cone=source_order()
    accepted={n.removeprefix(FAMILY).replace(".","/") for n in cone if n.startswith(FAMILY)}
    prior={n for n in cone if not n.startswith(FAMILY)}
    check(accepted==set(report["modules"]) and len(accepted)==696,"Final polynomial dependency closure")
    previous={r["module"]:r["source_sha256"] for r in json.loads(OLD.read_bytes())["completed"]}
    check(len(prior)==254 and prior<=previous.keys() and len(previous)==264,"Inherited source closure")
    for name,checksum in previous.items():
        check(digest(source(name))==checksum,"Prior source at "+name)

    fields=Counter()
    seen_fields=set()
    binaries={}
    peak=0.0
    field_re=re.compile(r"^noncomputable def evidence([23])(Ordinary|Tilted)(\d{3})\s*:\s*ReferenceEvidence\b",re.M)
    for name,row in rows.items():
        module=FAMILY+name.replace("/",".")
        src=source(module)
        check(digest(src)==row["source_sha256"] and row["status"]=="passed" and row["exit_code"]==0,"Source or status at "+name)
        log=PROJECT/row["log"]
        job=log.with_suffix(".job.json")
        check(digest(log)==row["log_sha256"] and digest(job)==row["metrics_sha256"],"Log or metrics at "+name)
        m=json.loads(job.read_bytes())
        check(m["process_completed"] and m["exit_code"]==0 and m["job_cap_MiB"]==6144
              and 0<float(row["peak_MiB"])==float(m["peak_job_MiB"])<=6144,"Resource record at "+name)
        if "artifact_sha256" in row:
            binaries["OddPiPowers/PolynomialValues/"+name+".olean"]=row["artifact_sha256"]
        if name in accepted:
            final=report["modules"][name]
            for key in ("source_sha256","log","log_sha256","metrics_sha256","peak_MiB","completed_at","artifact_sha256"):
                check(final.get(key)==row.get(key),"Acceptance record mismatch at "+name)
            direct=[n.removeprefix(FAMILY).replace(".","/") for n in local_imports(module) if n.startswith(FAMILY)]
            check(direct==final["local_imports"],"Import mismatch at "+name)
            peak=max(peak,float(row["peak_MiB"]))
            for d,k,i in field_re.findall(src.read_text(encoding="utf-8")):
                w=(d+k,int(i))
                check(w not in seen_fields,"Duplicate field "+str(w))
                seen_fields.add(w)
                fields[d+k]+=1
    expected={"2Ordinary":104,"2Tilted":7,"3Ordinary":93,"3Tilted":4}
    check(dict(fields)==expected==report["reference_fields"]
          and all((k,i) in seen_fields for k,n in expected.items() for i in range(n)),"Field coverage")
    check(peak==report["peak_job_MiB"]==5600.86,"Peak in final proof closure")
    check(len(binaries)==701 and sum("artifact_sha256" in report["modules"][n] for n in accepted)==695,"Artifact counts")
    with ZipFile(ARCHIVE) as z:
        check(len(z.namelist())==len(binaries) and set(z.namelist())==set(binaries),"Archived binary inventory")
        for member,checksum in binaries.items():
            check(sha256(z.read(member)).hexdigest()==checksum,"Archived binary at "+member)
    src=source(PUBLIC).read_text(encoding="utf-8")
    actual=re.findall(r"^example : (.+) := (\w+)$",src,re.M)
    check(actual==[(sig,n.rsplit(".",1)[-1]) for n,sig in SIGNATURES.items()],"Public signature checks in source")
    check_axioms((PROJECT/rows["PolynomialEndpointsAudit"]["log"]).read_text(encoding="utf-8"))
    print("Verified four public signatures and their recorded transitive axiom reports.")
    print("Final proof: 696 polynomial modules (695 emitted) and 254 inherited local imports.")
    print("Complete queue: 725 checked inputs, 701 archived object hashes and 208 concrete reference fields.")


if __name__=="__main__":
    main()
