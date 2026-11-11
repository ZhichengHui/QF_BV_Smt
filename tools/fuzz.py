#!/usr/bin/env python3
"""Differential test of bvsmt against z3 on random QF_BV problems.

Usage: fuzz.py BVSMT Z3 N [SEED]

For each random problem: both solvers must agree on sat/unsat, and for sat the model printed by
bvsmt, added to the problem as assertions, must be satisfiable for z3.
"""
import random
import subprocess
import sys

BIN = ["bvand", "bvor", "bvxor", "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv",
       "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvnand", "bvnor", "bvxnor"]
ASSOC = ["bvand", "bvor", "bvxor", "bvadd", "bvmul"]
UN = ["bvnot", "bvneg"]
CMP = ["=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]


def const(w):
    r = random.random()
    if r < 0.6:
        return "#b" + "".join(random.choice("01") for _ in range(w))
    if r < 0.8 and w % 4 == 0:
        return "#x" + "".join(random.choice("0123456789abcdef") for _ in range(w // 4))
    return "(_ bv%d %d)" % (random.randrange(2 ** w), w)


def bv(vs, w, d):
    """A term of width w."""
    cands = [v for v, vw in vs if vw == w]
    if d == 0 or random.random() < 0.25:
        if cands and random.random() < 0.7:
            return random.choice(cands)
        return const(w)
    r = random.random()
    if r < 0.40:
        return "(%s %s %s)" % (random.choice(BIN), bv(vs, w, d - 1), bv(vs, w, d - 1))
    if r < 0.45:
        return "(%s %s %s %s)" % (random.choice(ASSOC), bv(vs, w, d - 1), bv(vs, w, d - 1), bv(vs, w, d - 1))
    if r < 0.53:
        return "(%s %s)" % (random.choice(UN), bv(vs, w, d - 1))
    if r < 0.61:
        return "(ite %s %s %s)" % (boolean(vs, d - 1), bv(vs, w, d - 1), bv(vs, w, d - 1))
    if r < 0.68 and w > 1:
        k = random.randint(1, w - 1)
        return "(concat %s %s)" % (bv(vs, w - k, d - 1), bv(vs, k, d - 1))
    if r < 0.76:
        big = w + random.randint(0, 3)
        lo = random.randint(0, big - w)
        return "((_ extract %d %d) %s)" % (lo + w - 1, lo, bv(vs, big, d - 1))
    if r < 0.82 and w > 1:
        k = random.randint(1, w - 1)
        return "((_ %s %d) %s)" % (random.choice(["zero_extend", "sign_extend"]), k, bv(vs, w - k, d - 1))
    if r < 0.85:
        return "((_ %s 0) %s)" % (random.choice(["zero_extend", "sign_extend"]), bv(vs, w, d - 1))
    if r < 0.89:
        divs = [k for k in range(1, w + 1) if w % k == 0]
        k = random.choice(divs)
        return "((_ repeat %d) %s)" % (w // k, bv(vs, k, d - 1))
    if r < 0.93:
        return "((_ %s %d) %s)" % (random.choice(["rotate_left", "rotate_right"]), random.randint(0, 2 * w), bv(vs, w, d - 1))
    if r < 0.96 and w == 1:
        k = random.randint(1, 4)
        return "(bvcomp %s %s)" % (bv(vs, k, d - 1), bv(vs, k, d - 1))
    return "(let ((t %s) (u %s)) (bvadd t (bvor u t)))" % (bv(vs, w, d - 1), bv(vs, w, d - 1))


def boolean(vs, d):
    r = random.random()
    if d == 0 or r < 0.4:
        w = random.randint(1, 4)
        return "(%s %s %s)" % (random.choice(CMP), bv(vs, w, max(d - 1, 0)), bv(vs, w, max(d - 1, 0)))
    if r < 0.5:
        w = random.randint(1, 4)
        return "(%s %s %s %s)" % (random.choice(["=", "distinct"]), bv(vs, w, max(d - 1, 0)),
                                  bv(vs, w, max(d - 1, 0)), bv(vs, w, max(d - 1, 0)))
    if r < 0.6:
        return "(not %s)" % boolean(vs, d - 1)
    if r < 0.7:
        return "(ite %s %s %s)" % (boolean(vs, d - 1), boolean(vs, d - 1), boolean(vs, d - 1))
    if r < 0.8:
        return "(%s %s %s %s)" % (random.choice(["and", "or", "=>"]), boolean(vs, d - 1), boolean(vs, d - 1), boolean(vs, d - 1))
    op = random.choice(["and", "or", "xor", "=>", "=", "distinct"])
    return "(%s %s %s)" % (op, boolean(vs, d - 1), boolean(vs, d - 1))


def problem():
    vs = [("v%d" % i, random.randint(1, 4)) for i in range(random.randint(1, 3))]
    decls = "".join("(declare-const %s (_ BitVec %d))\n" % v for v in vs)
    funs = ""
    if random.random() < 0.3:
        w = random.randint(1, 4)
        funs = "(define-fun f ((a (_ BitVec %d)) (b (_ BitVec %d))) (_ BitVec %d) %s)\n" % (
            w, w, w, bv([("a", w), ("b", w)], w, 2))
        vs2 = vs + [("(f %s %s)" % (bv(vs, w, 1), bv(vs, w, 1)), w)]
    else:
        vs2 = vs
    asserts = "".join("(assert %s)\n" % boolean(vs2, 3) for _ in range(random.randint(1, 3)))
    return "(set-logic QF_BV)\n" + decls + funs + asserts + "(check-sat)\n"


def run(cmd, src):
    return subprocess.run(cmd, input=src, capture_output=True, text=True, timeout=300).stdout


def main():
    bvsmt, z3, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    stats = {"sat": 0, "unsat": 0}
    for k in range(n):
        p = problem()
        ours = run([bvsmt], p + "(get-model)\n").split("\n")
        theirs = run([z3, "-in"], p).strip()
        if ours[0] != theirs:
            print("MISMATCH (bvsmt %s, z3 %s):\n%s" % (ours[0], theirs, p))
            sys.exit(1)
        stats[theirs] += 1
        if theirs == "sat":
            model = "\n".join(l.strip() for l in ours[1:] if l.strip().startswith("(define-fun"))
            check = p.replace("(check-sat)\n", "") + model.replace("(define-fun ", "(define-fun m_") + "\n"
            for line in ours[1:]:
                line = line.strip()
                if line.startswith("(define-fun"):
                    name = line.split()[1]
                    check += "(assert (= %s m_%s))\n" % (name, name)
            check += "(check-sat)\n"
            if run([z3, "-in"], check).strip() != "sat":
                print("BAD MODEL:\n%s\n%s" % (p, "\n".join(ours)))
                sys.exit(1)
    print("ok: %d problems, %d sat, %d unsat" % (n, stats["sat"], stats["unsat"]))


main()
