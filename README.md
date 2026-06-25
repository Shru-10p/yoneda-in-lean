# Yoneda Lemma in Lean 4

A formalization of the **Yoneda Lemma** in Lean 4 from scratch (no external libraries)

## The Theorem

For a *locally small* category $\mathbf{C}$ and a presheaf $F : \mathbf{C}^{\mathrm{op}} \to \mathbf{Type}_v$:

$$\mathrm{Nat}(\mathrm{Hom}(-, A),\, F) \;\simeq\; F(A)$$

naturally in both $A \in \mathbf{C}$ and $F \in [\mathbf{C}^{\mathrm{op}}, \mathbf{Type}_v]$.

>The isomorphism is also sometimes written as $\left(\prod_{X \in \mathbf{C}}{\mathrm{Hom}(X, A)} \to F(X)\right)\;\simeq\; F(A)$. in type-theoretic contexts, see [A Type theoretical Yoneda lemma](https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/).

## Why `Type` instead of `Set`?

In the classical statement, the target of the presheaf is $\mathbf{Set}$, but this formalization uses Lean's `Type v` instead because:

**$\mathbf{Set}$ is not primitive in Lean 4**

Lean is based on [dependent type theory](https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/#dependent-type-theory). There is no ambient universe of "all sets" to quantify over. Lean's `Set α` is actually notation for `α → Prop` which is very different from the category-theoretic $\mathbf{Set}$.

**Universe levels replace the large/small distinction**

In set-theoretic foundations, the distinction between *small* and *large* is handled by Grothendieck universes or by separating sets from classes. In Lean 4 this is handled by *universe polymorphism*: `Type v` is a type universe at level `v`, and is iteself a type, but lives in the next higher universe (`Type v : Type (v+1)`).
>A category is **locally small** in the sense used here when its objects live in `Type u`, and each hom-set lives in `Type v`. The representable presheaf `Hom(-, A) : Cᵒᵖ ⥤ TypeCat.{v}` then maps into `Type v`, exactly as the hom-sets do - so everything is universe-consistent without invoking any large-cardinal axioms.

**The result is strictly more general**

The version with `Type` subsumes the version with `Set`: any $\mathbf{Set}$-valued presheaf is a special case of a `Type`-valued one (since a set is a type). In addition, the type-theoretic version works for presheaves valued in *any* type universe, including higher types (groupoids, $\infty$-groupoids, etc.), which is the foundation of modern formalizations in HoTT and condensed mathematics.
