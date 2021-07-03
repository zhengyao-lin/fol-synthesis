FOL-LFP synthesis
---

### Requirements

```
python3 -m pip install z3-solver==4.8.8.0
```

### Examples

Currently these examples work: `examples/bst.py`, `examples/list.py`, `examples/dlist.py`

For instance,
```
$ python3 examples/bst.py
synthesizing formulas with 0 hypothesis(es)
synthesizing formulas with 1 hypothesis(es)
    bst(x0) => btree(x0)
synthesizing formulas with 2 hypothesis(es)
    ne(x0, nil) /\ bst(x0) => bst(left(x0))
    ne(x0, nil) /\ btree(x0) => bst(left(x0))
    ne(x0, nil) /\ btree(x0) => bst(right(x0))
synthesizing formulas with 3 hypothesis(es)
    leftmost(x0, v) /\ ne(x0, nil) /\ bst(x0) => le(v, key(x0))
```

where
 - `examples/bst.py` uses counterexample size of 3
 - `examples/list.py` uses counterexample size of 5
 - `examples/dlist.py` uses counterexample size of 5

### Synthesizing for a different theory

Import everything in `synthesis.py` and initialize a `Z3Environment`
```
from synthesis import *
env = Z3Environment(None)
```

Start with an unsorted language:
```
language = Language(
    { "nil": 0, "n": 1 },
    {
        "list": 1,
        "lseg": 2,
    },
)
```
where the first dictionary denotes functions with arities,
and the second dictionary denotes relations with arities.

We can initialize a (horn clause) synthesizer with
```
synthesizer = HornClauseSynthesizer(
    env, language,
    # parameters
    hypothesis_term_depth=0,
    conclusion_term_depth=0,
    max_num_vars=3,
    max_num_hypotheses=2,
    allow_equality_in_conclusion=True,
)
```
In this case, it will try to synthesize formulas of the form
```
ph1 /\ ph2 => ph3
```
where `ph1`, `ph2`, `ph3` are atomic formulas with 0 term depth (i.e. only variables can be terms), and number of universally quantified variables bounded by 3.

Before synthesizing, we need to specify two symbolic counterexapmles:
 - One counterexample used in synthesis to make sure the formula is NOT FO-provable.
 - One (finite) counterexample used in verification of synthesized formulas

See `examples/list.py` for more details of these two structures (they are `syn_counterexample_unrolled` and `ver_counterexample` respectively in the example).

Furthmore, we can also add constraints on any subterm or subformula.
For example
```
# n(nil) should not be a subterm
synthesizer.dismiss_term(Application.parse("n(nil)"))

# btree() should not be applied to any appliation of key
synthesizer.dismiss_atomic_formula(Application.parse("btree(key(<any>))"))
```
These are current workarounds for many-sorted/UCT languages.

Finally we can start synthesizing by
```
for formula_string in synthesizer.synthesize():
    print(formula_string)
```
