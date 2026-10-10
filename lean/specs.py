"""The certified points and their printed claims, copied from the output of the scripts in certificates/
(make certificates). gen.py turns each entry into a positive theorem and its negative controls."""
PAPER = {"boxes": "rho", "enc": "full"}
T4 = {"boxes": "exact", "enc": "pruned"}
EXACT_FULL = {"boxes": "exact", "enc": "full"}

L1 = [
    {"name": "L1_paper", "kind": "l1", "p": {"c": "21.178", "th": "0.10488", "eps": "0.05620", "de": "0.026384", **PAPER},
     "claims": {"s0": "0.003431999", "b3": "1.996568001", "bA": "2.996568001", "o3": "1.99657", "oA": "2.99657"},
     "doc": "certify_L1.py, paper lemmas (rho boxes, full encoding)."},
    {"name": "L1_paper_exact", "kind": "l1", "p": {"c": "21.178", "th": "0.10488", "eps": "0.05620", "de": "0.026384", **PAPER},
     "claims": {"s0": "0.003432", "b3": "1.996568", "bA": "2.996568", "o3": "1.99657", "oA": "2.99657"},
     "doc": "certify_L1.py, paper lemmas: the exact saving 0.003432 (the same-block term eps - 2 delta binds)."},
    {"name": "L1_T4", "kind": "l1", "p": {"c": "20.276", "th": "0.10457", "eps": "0.05961", "de": "0.027966", **T4},
     "claims": {"s0": "0.003677999", "b3": "1.996322001", "bA": "2.996322001", "o3": "1.99633", "oA": "2.99633"},
     "doc": "certify_L1.py, exact count + pruned encoding."},
    {"name": "L1_T4_exact", "kind": "l1", "p": {"c": "20.276", "th": "0.10457", "eps": "0.05961", "de": "0.027966", **T4},
     "claims": {"s0": "0.003678", "b3": "1.996322", "bA": "2.996322", "o3": "1.99633", "oA": "2.99633"},
     "doc": "certify_L1.py, exact count + pruned encoding: the exact saving 0.003678."},
]

DERAND = [
    {"name": "derand_T4", "kind": "derand", "p": {"c": "21.27327", "th": "0.111731", "eps": "0.05684608", **T4},
     "claims": {"s0": "0.003999289713", "b3": "1.996000711", "bA": "2.996000711", "o3": "1.996001", "oA": "2.996001"},
     "doc": "derand_cert.py, exact count + pruned encoding: Theorem 1, det 3SUM O(n^1.996001), APSP O(n^2.996001)."},
    {"name": "derand_T1", "kind": "derand", "p": {"c": "22.21832", "th": "0.112064", "eps": "0.05351255", **PAPER},
     "claims": {"s0": "0.003709895012", "b3": "1.996290105", "bA": "2.996290105", "o3": "1.996291", "oA": "2.996291"},
     "doc": "derand_cert.py, paper lemmas: det 3SUM O(n^1.996291), APSP O(n^2.996291)."},
    {"name": "derand_paper_point", "kind": "derand", "p": {"c": "21", "th": "1/9", "eps": "1/18", **PAPER},
     "claims": {"s0": "0.003555565103", "b3": "1.996444435", "bA": "2.996444435", "o3": "1.996445", "oA": "2.996445"},
     "doc": "derand_cert.py, the paper point (21, 1/9, 1/18)."},
]

def _et(name, c, th, a, eps, eta, kind, s0, b3, bA):
    return {"name": name, "kind": "et", "p": {"c": c, "th": th, "a": a, "eps": eps, "eta": eta, **kind},
            "claims": {"s0": s0, "b3": b3, "bA": bA}, "doc": f"certify.py {name[3:]} (params.json)."}
ET = [
    _et("ET_paper_lemmas", "22.21828", "0.112064", "0.5", "0.0535127", "0.03466378", PAPER,
        "0.001854952", "1.999072524", "2.999381683"),
    _et("ET_exact_count", "20.78856", "0.112251", "0.5", "0.05724277", "0.03437513", EXACT_FULL,
        "0.001967727", "1.999016137", "2.999344091"),
    _et("ET_exact_count_free_density", "21.38155", "0.116562", "0.518518", "0.05561926", "0.03703601", EXACT_FULL,
        "0.002059888", "1.998970056", "2.999313371"),
    _et("ET_exact_count_free_density_pruned_encoding", "21.91529", "0.116108", "0.51898", "0.05519776", "0.03796", T4,
        "0.002095234", "1.998952383", "2.999301589"),
    _et("ET_paper_point", "21", "1/9", "0.5", "1/18", "0.032", PAPER, "0.001777777", "1.999111112", "2.999407408"),
    _et("ET_paper_point_eps_R21", "21", "1/9", "0.5", "0.0566745", "0.032", PAPER, "0.001813583", "1.999093209", "2.999395473"),
]

SPECS = L1 + DERAND + ET
