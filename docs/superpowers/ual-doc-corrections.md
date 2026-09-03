# Corrections to the UAL design document

The UAL specification is a Google Doc, which cannot be edited from this
repository. This is the list to hand to its authors.

Items 1–7 are spec §9 of
`docs/superpowers/specs/2026-08-24-ual-extended-blueprints-design.md`, found
while designing and building the extraction pipeline. Items 8 and 9 came out of
the acceptance check in `docs/superpowers/ual-linear-vesting-acceptance.md`,
which hand-wrote the document pair for a real verified contract and asked
whether it carried what the proofs need; they are the two places where the
answer was no *because of the annotation syntax* rather than because of a
document format.

Each item says which section it concerns, what that section currently says, what
it should say, the evidence, and where the implementation in this repository
stands. Section numbers are the UAL doc's own.

Three items (1, 8, 9) ask for changes to what UAL *means*, not just how it is
spelled. The other six are corrections of things that are simply wrong or
under-specified.

---

## 1. §4: `#prep_uplc` is superseded by a per-function wrapper

**Currently says.** §4 elaborates an annotated program through `#prep_uplc`,
with a step bound (`#prep_uplc … 5000`).

**Should say.** The current Lean shape imports the CIP-57 blueprint and states
theorems against an application of the compiled program. The generalisation
UAL's refined signature implies is a **per-function wrapper**, one per `ONCHAIN`
block, applying the program to its declared arguments in order:

```lean
def mintingContract (cs : CurrencySymbol) (ctx : ScriptContext) : HaltState :=
  cekExecuteProgram MyBp.mintingContract.script [toTerm cs, toTerm ctx] 1883313
```

That is what makes UAL's own `isSuccessful (mintingContract cs ctx)` elaborate.
`validatorAccepts` is the single-argument special case of it.

**Evidence.** The wrapper needs exactly two things the annotation already
carries and the blueprint can now transport: the ordered argument list with its
encodings, and an execution bound. Those are the `arguments` and `budget`
validator fields this slice adds (spec §5). Nothing else in the pair is needed
to write it.

**Caution on the bound.** The `1883313` above is an `exCPU` figure substituted
into a slot that takes a CEK **step** count. Those are different units and
neither determines the other without the cost model. The design document should
not show the substitution as if it were sound; see item 7 and
`ual-linear-vesting-acceptance.md` §3.2, which found that the Lean library
already has a budget-aware evaluator (`cekExecuteProgramWithBudget`) consuming
exactly the `exCPU`/`exMem` pair UAL declares.

**This implementation.** Not applicable — this slice emits the documents; the
wrapper is generated in slice 2. `arguments` and `budget` exist and are emitted.

---

## 2. §4: the import direction is inverted

**Currently says.** "if a module M1 imports a module M2 … the elaborated Lean4
module M2Predicates will import Lean4 module M1Predicates".

**Should say.** M1 depends on M2, so `M1Predicates` imports `M2Predicates`. The
dependency edge points the way the surface language's edge points.

**Evidence.** Reversing it makes the generated project fail to elaborate: the
definitions M1's predicates use would not be in scope, and a module cannot
import something that imports it. As written, a two-module contract produces a
cycle.

**This implementation.** Follows the corrected form.
`PlutusTx.Assurance.Build` sets a fragment's `imports` from its own module's
import list (`Build.hs:92`), so the fragment for M1 imports the fragment for M2.
The direction is also enforced: the same module rejects a cyclic set
(`findCycle`, `Build.hs:145`).

---

## 3. §2.2, §2.3, §2.4: the closing delimiter `-@}` does not compile

**Currently says.** `{-@ … -@}` in §2.2, §2.3 and §2.4. (§2.1's example already
uses `@-}`, so the document is internally inconsistent as well as wrong.)

**Should say.** `{-@ … @-}` — at-sign, dash, closing brace. Standardise on it
throughout.

**Evidence.** `-@}` contains no `-}`, so it does not terminate a Haskell block
comment. Every annotated file written the document's way fails to lex, and the
error points at the *opening* of the comment, which is a long way from the typo:

```
$ printf 'module D1 where\n{-@ ONCHAIN foo -@}\nfoo :: Int\nfoo = 1\n' > D1.hs
$ ghc -fno-code D1.hs

D1.hs:2:1: error: [GHC-21231] unterminated `{-' at end of input
  |
2 | {-@ ONCHAIN foo -@}
  | ^^^^^^^^^^^^^^^^^^^...
```

Reproduced with GHC 9.6.7 from this repository's devshell.

**And say one thing more.** Aiken and Scalus have different comment syntaxes, so
a single delimiter pair cannot work in all three surface languages. The document
should say that each surface language defines its own delimiter pair around the
same block grammar, rather than presenting one spelling as universal.

**This implementation.** Follows the corrected form, and says so where someone
would otherwise "fix" it back:
`PlutusTx.Ual.Lexer.blockClose = "@-}"` (`Lexer.hs:31`), with a Haddock note
recording that the design document has it the other way round.

---

## 4. §2.4: `PROPERTY` needs a natural-language field

**Currently says.** A `PROPERTY` block carries a name and a formal statement.

**Should say.** It carries a name, a **required** natural-language statement,
and the formal statement:

```
{-@ PROPERTY p_no_locked_funds
      "Funds cannot be locked: the beneficiary can always claim."
    : ∀ …
@-}
```

**Evidence.** The assurance document's `statement.text` is REQUIRED
(CIP-XXXX, "Statements": *"The natural-language `text` is deliberately
mandatory: every reader of an assurance document can understand every claim,
whatever tooling they have."*). There is no other source for it — a producer
cannot derive prose from a formal statement — so an annotation without this
field cannot produce a conforming document at all.

**This implementation.** Follows the corrected form, and enforces it. A
`PROPERTY` block with no quoted statement is a parse error, not a defaulted
empty string: `MalformedBlock … "expected a quoted natural-language statement
after the name"` (`Parser.hs:242`).

---

## 5. §2.2: the refined signature has no argument names

**Currently says.** A refined signature gives argument *types*
(`{ CurrencySymbol : asData } -> …`) and no names.

**Should say.** Say so explicitly, and say what follows: everything downstream
of the annotation is positional. A consumer that wants named wrapper parameters
invents the names itself.

**Evidence.** There is no second source to fall back on. Template Haskell's
`reify` does not expose a Haskell function's parameter names, so the pipeline
could not recover them even if it wanted to; inventing them at extraction time
would put fabricated names in a published document.

**This implementation.** Follows the corrected form, deliberately. Blueprint
`arguments` entries carry an `encoding` and a `schema` and nothing else, with
the reason at the type: *"Positional and unnamed: the element carries only an
encoding and a schema"* (`Blueprint/Validator.hs:68`). Spec §5 records the
consequence.

---

## 6. §2.2's `PlutusV4` and §2.3's `IsScott` are ahead of the Lean side

**Currently says.** `[version: PlutusV4]` is a legal option, and `asScott`
arguments elaborate through an `IsScott` class.

**Should say.** Both are forward-looking. The document should mark them as such
rather than as available, and name what has to land first:

- `PlutusV4`: the Lean parser's `plutusVersionToLangExpr` errors past V3.
- `IsScott`: `CardanoLedgerApi` has `IsData` (`IsData/Class.lean`) and no
  `IsScott` at all, so an `asScott` argument has nothing to elaborate through.

**Evidence.** Upstream Lean dependency in both cases; neither is a UAL problem
to solve, but a user reading the document has no way to find that out.

**This implementation.** Deferred, in a specific and slightly awkward way that
the document should acknowledge: both are **accepted by the front end and not
consumable downstream**. `parseVersion` accepts `PlutusV4` (`Parser.hs:93`) and
`parseEncoding` accepts `asScott` (`Parser.hs:165`), and both then travel into
the emitted documents. So the format admits values no consumer can yet act on.
That is the right choice for a syntax that outlives its first consumer, but it
means the *document*, not the parser, is where a reader learns which values are
real today. Spec §8.4 records both as out of scope for this slice.

---

## 7. §2.1's open comment thread: why write predicates in Lean?

**Currently says.** An unresolved comment thread asks why users would write
predicates in Lean rather than in their original language.

**Should say.** Record it as decided in favour of UAL for now, and record why
the decision is cheap to revisit: nothing in the design forecloses a
Haskell-to-Lean predicate compiler later. Such a compiler would be an additional
front end producing the same `formalFragments` — the assurance document is the
interface, and it does not care how the fragment source was written.

**This implementation.** Follows, trivially: `PREDICATE` bodies are
pass-through text, never interpreted. Which is also the honest limit of it —
**nothing in this repository typechecks the Lean in a `PREDICATE` or `PROPERTY`
block.** A body with a syntax error travels into the assurance document
unchanged and fails for the first time in slice 2. The design document should
not imply that annotating a contract validates the annotations.

---

## 8. §2.1: no `PROPERTY` can name the validator it is about

This item and the next are the two the acceptance check turned up. Both are
additions rather than corrections, and both are cheaper now than after the CIP
is published.

**Currently says.** Nothing. A `PROPERTY` body is an arbitrary proposition. UAL
reserves no identifier for "the program this property is scoped to", and defines
no acceptance or rejection predicate over it.

**Should say.** Specify the naming contract. Either:

- **(a)** every id in the property's scope is bound as an in-scope name in the
  formal statement, together with an acceptance predicate over it; or
- **(b)** each `ONCHAIN` block emits the wrapper of item 1 under a stated name,
  and properties refer to that.

(b) is the better fit, because item 1's wrapper has to exist anyway and already
has a name and an arity.

**Evidence.** Without it, a property cannot mention the code it is about, and
the failure is silent. Every theorem in the reference project mentions the
compiled program — `Soundness.lean:163` is `validatorAccepts ctx spendValidator`
— and this pipeline's own worked example, having no way to name it,
axiomatises the script's behaviour instead
(`doc/docusaurus/static/code/Example/Ual/Blueprint/Main.hs:170`):

```lean
axiom verdict : GovAction → Verdict
```

and states all five of its properties about `verdict`. Those properties are
provable without the script existing. They are well-formed, they carry a real
natural-language claim, no checker rejects them — and they constrain no compiled
code. That is the worst failure mode a specification language can have, and it
is what the absence of a naming contract produces by default.

**Where the other half of the fix went.** The CIP now requires a
`formal.language` specification to define how the validators named in
`scope.validators` are denoted inside a formal statement, and recommends it
define acceptance/rejection (CIP-XXXX, "Statements"). That obligation is
language-agnostic, which is all a language-neutral format can say; **UAL is the
language it now falls to.** This item is that obligation discharged.

**This implementation.** Does not solve it, and cannot: with no syntax to
express the binding, `buildAssurance` has nothing to emit. The worked example's
`axiom verdict` is the visible consequence and should be revisited once the
contract is written down.

---

## 9. §2.1: `PROPERTY` blocks carry no clauses, so scope and `uses` are guessed

**Currently says.** A `PROPERTY` block is a name, a statement and a body. It has
no clause syntax at all — no scope, no dependency list.

**Should say.** Add a bracketed clause group to `PROPERTY`, in the same style
`ONCHAIN` already uses for `[version: …]` and `[exCPU: …, exMem: …]`:

```
{-@ PROPERTY [scope: spendValidator] p_cancel_sound "…" : … @-}
```

with at least `scope:` and, optionally, `uses:`. Both are per-property facts
that today have to be supplied per *invocation* or guessed from module layout.

**Evidence, scope.** A producer with no per-property scope must apply one scope
to every property it emits. For a single-validator contract that is merely
coarse. For a multi-validator contract it is **false**: properties about
validator B are published as claims about validator A, and no consumer can
detect it, because a well-formed scope naming a real validator is exactly what a
correct document looks like.

This is not hypothetical for the acceptance check's own reference contract.
`aiken build` emits *two* validators for linear vesting —
`linear_vesting.linear_vesting.spend` and `linear_vesting.linear_vesting.else`
— sharing one `compiledCode`, and the proofs target only `spend`
(`ual-linear-vesting-acceptance.md` §3.5). A single global scope happens to
survive that case, since the properties really are all about `spend`, but only
by luck of which validator the caller named.

A second, narrower half: the reference contract also has six theorems about the
pure schedule arithmetic (`vested_le_total`, `vested_mono`, …) that belong to no
validator. Those need something the annotation syntax cannot express *and* a CIP
change, so they are recorded as future work in the CIP's "Validators only"
rather than fixed here — but a `scope:` clause is the annotation half of it, and
until it exists the only way to publish such a theorem is to scope it falsely,
which the CIP now forbids outright.

**Evidence, `uses`.** A property's fragment dependencies are currently inferred
as "my own module's fragment, if it has one". A module carrying `PROPERTY`
blocks and no `PREDICATE` block therefore emits properties with an empty `uses`,
and a consumer has nothing to import (`Build.hs:114` against `:83`). The author
avoids this by putting predicates and properties in the same module — which is
a spec obligation nobody has written down, not a property of the design.

**This implementation.** Does not solve either, and is candid about it in the
source. Scope: `propertyValidators = [defaultValidator]` for every property
(`Build.hs:106`), from a single argument to `buildAssurance`. `uses`:
`formalUses = [mname | Set.member mname fragmentIds]` (`Build.hs:114`), with the
Haddock at `Build.hs:99` recording that *"`PropertyDecl` has no `uses` field, so
the annotation cannot ask for one."* Both wait on the syntax.

Related, and worth fixing in this repository whether or not UAL changes:
`buildAssurance` never checks its scope argument against the blueprint's
validator ids, unlike `attachUal`'s corresponding checks, so a scope naming no
validator reaches the generator with no diagnostic.

---

## Summary

| # | UAL doc | Kind | This implementation |
| --- | --- | --- | --- |
| 1 | §4 `#prep_uplc` | superseded | n/a — slice 2 |
| 2 | §4 import direction | wrong | follows, and enforces acyclicity |
| 3 | §2.2–2.4 `-@}` | does not compile | follows `@-}` |
| 4 | §2.4 natural-language field | missing | follows, and requires it |
| 5 | §2.2 argument names | under-specified | follows: positional |
| 6 | §2.2 `PlutusV4`, §2.3 `IsScott` | ahead of Lean | parsed, not consumable |
| 7 | §2.1 comment thread | unresolved | follows; nothing typechecks bodies |
| 8 | §2.1 naming the validator | **missing feature** | blocked on the syntax |
| 9 | §2.1 `PROPERTY` clauses | **missing feature** | blocked on the syntax |
