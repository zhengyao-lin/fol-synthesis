Logic Synthesis
---

## First-order Logic

In `synthesis/fol/base`, we define the usual concepts of many-sorted first-order logic, such as languages, formulas, and structures.

For example, a language is simply a collection of sorts, function symbols, and relation symbols:
```
class Language:
    sorts: Tuple[Sort, ...]
    function_symbols: Tuple[FunctionSymbol, ...]
    relation_symbols: Tuple[RelationSymbol, ...]
```

### Syntax

The syntax of FOL is defined in `synthesis/fol/base/syntax.py` in a straightforward way.

### Semantics

For structures (see `synthesis/fol/base/semantics.py`), we first abstract carrier sets as follows:
```
class CarrierSet(ABC):
    def get_smt_sort(self) -> smt.SMTSort: ...

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...
```

For instance, a concrete implementation of a finite carrier set is
```
class FiniteCarrierSet(CarrierSet):
    sort: smt.SMTSort
    domain: Tuple[smt.SMTTerm, ...]

    def get_smt_sort(self) -> smt.SMTSort:
        return self.sort

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.And(*(formula.substitute({ variable: element }) for element in self.domain))

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Or(*(formula.substitute({ variable: element }) for element in self.domain))
```

A structure is then an interpretation of the symbols in SMT that maps sort symbols to carrier sets, function symbols and relation symbols to SMT functions (which are Python functions taking SMT terms and returning an SMT term):
```
class Structure:
    language: Language
    carriers: Mapping[Sort, CarrierSet]
    function_interpretations: Mapping[FunctionSymbol, smt.SMTFunction]
    relation_interpretations: Mapping[RelationSymbol, smt.SMTFunction]
```

Then, every logical connective implements an interpretation function with the following signature
```
def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm: ...
```
which returns an SMT constraint expressing that the formula is valid in the given structure and valuation.

For example, `Conjunction` in `synthesis/fol/base/syntax.py` implements `interpret` as:
```
def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
    return smt.And(
        self.left.interpret(structure, valuation),
        self.right.interpret(structure, valuation),
    )
```

## Synthesizing Formulas

The key notion in the implementation that enables synthesis and that I couldn't find a good name for (or I don't know what's the standard name for it) is what I'm currently calling "templates". They generalize the concrete formulas and structures to symbolic formulas (formula schema?) and structures. At the same time, interpretation in a structure, substitution, and free variables can be defined on these templates as well.

Examples of these formula and structure "templates" can be found in `synthesis/fol/templates`.

For example, `AtomicFormulaTemplate` represents an atomic formula with a bound on the depth of terms.
They can be composed with regular connectives as well to build more complicated templates, for example:
```
Implication(
    AtomicFormulaTemplate(language, (x, y, z), 1),
    AtomicFormulaTemplate(language, (x, y), 2),
)
```
is a formula template for `φ(x, y, z) -> ψ(x, y)` for some formulas `φ` with depth 1 terms and `ψ` with depth 2 terms.

Then, the interpretation function is also implemented for `AtomicFormulaTemplate`, allowing one to express the SMT constraint that such formula schema is valid in some structure:
```
Implication(
    AtomicFormulaTemplate(language, (x, y, z), 1),
    AtomicFormulaTemplate(language, (x, y), 2),
).interpret(<some structure>, { x: ..., y: ..., z: ... })
```
Given this SMT constraint, an SMT solver may produce an SMT model in which in this is true.
In such case, we can use the following method implemented by any template:
```
def get_from_smt_model(self, model: smt.SMTModel) -> T: ...
```
to obtain a concrete formula from the SMT model.

## Synthesizing Structures

Similar concept is implemented for structures as well.
For example, `FiniteFOModelTemplate` implements both `Structure` and `Template[Structure]`
```
class FiniteFOModelTemplate(Structure, Template[Structure]): ...
```
and this template represents a finite model of some theory, but the interpretations of function/relation symbols are represented using uninterpreted functions or constants in SMT.

Then one can, for example, interpret a formula (or potentially a formula template) on this structure
```
structure = FiniteFOModelTemplate(theory, { sort_a: 3 }) # this bounds the size of the carrier set of sort A to 3
<some formula>.interpret(structure, {})
```

And note that `FiniteFOModelTemplate` also implements the `get_from_smt_model` method, which allows one to produce a concrete finite structure from any SMT model.


## Example: a Counterexample Guided Synthesizer for Formulas

`synthesis/fol/cegis.py` contains a procedure with input:
1. A formula template `φ`
2. A structure template `M`
3. A structure template `N`

Intuitively `M` and `N` describe two classes of structures.

Then the procedure synthesizes all concrete formulas described by `φ` that is true for all models in `M` but is not true for some model in `N`.

In the example `examples/list.py`, `M` describes the finite LFP models of a given theory:
```
M = FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 })
```
and `N` describes the structures in which if the formula `φ` is FO-provable after unfolding the fixpoint definitions twice, then `φ` would hold in `N`:
```
N = FOProvableStructureTemplate(theory, unfold_depth=2)
```

In another example `examples/group.py`, we take
```
M = FiniteFOModelTemplate(ab_group_theory, size_bounds={ sort_group: 8 })
N = FiniteFOModelTemplate(group_theory, size_bounds={ sort_group: 8 })
```
where `ab_group_theory` is the theory of Abelian groups and `group_theory` is the theory of groups.
