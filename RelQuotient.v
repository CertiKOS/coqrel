Require Import LogicalRelations.

(** * Quotient set for a relation *)

(** Although Rocq's setoid rewriting support is helpful when we wish
  to consider a type up to a given equivalence relation, it can
  sometimes be useful to use a quotient type where equivalent values
  are considered equal. Sometimes this quotient type
  can be defined separately, so that it contains a canonical
  representative for each equivalence class.
  However, this is not always possible or worth the effort.

  If we accept the use of the predicate extensionality and proof
  irrelevance axioms, another option is to use a more traditional
  definition of equivalence classes,
  as predicates on the base type ("subsets")
  satisfying certain properties. This is what we do here. *)

Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.

(** It should be noted that the elements of the quotient are
  "non constructive". [explain] *)

(** ** Definition *)

(** We use a fairly versatile way to define equivalence classes.
  Elements of [quotient R] as defined below are essentially the
  preimage sets induced by [R]. When [R] is an equivalence relation,
  this will correspond to the usual definition.
  However, the construction is meaningful in other cases.
  For example, when [R] is a preorder the construction gives the
  associated partial order. *)

Record quotient {A B} {R : rel A B} :=
  {
    in_eqcl : A -> Prop;
    in_eqcl_wf : exists b, forall a, in_eqcl a <-> R a b;
  }.

Arguments quotient {A B} R.

Local Obligation Tactic := solve [rauto | firstorder].

(** Obtaining the equivalence class associated with
  an element of the base type is straightforward. *)

Program Definition eqcl {A B} (R : rel A B) (b : B) : quotient R :=
  {| in_eqcl a := R a b |}.

Global Instance eqcl_params :
  Params (@eqcl) 1 := {}.

(** ** Ordering *)

(** The preimage sets used to define the [quotient] type can be
  ordered by inclusion. *)

Definition qle {A B} {R : rel A B} : relation (quotient R) :=
  fun x y => forall a, in_eqcl x a -> in_eqcl y a.

(** The induced ordering is always a partial order, no matter what
  properties [R] may or may not have. *)

Global Instance eqcl_le_preo {A B} (R : rel A B) :
  PreOrder (@qle A B R).
Proof.
  firstorder.
Qed.

Global Instance eqcl_le_po {A B} (R : rel A B) :
  PartialOrder eq (@qle A B R).
Proof.
  intros x y. cbn.
  split.
  - intros [ ]. firstorder.
  - unfold flip, qle. intros [Hxy Hyx].
    destruct x as [x [xa Hx]], y as [y [ya Hy]]; cbn in *.
    cut (x = y). { intro. subst. f_equal. apply proof_irrelevance. }
    apply functional_extensionality. intros a.
    apply propositional_extensionality. firstorder.
Qed.

(** ** Properties *)

(** The exact nature of the constructions we have defined depend
  largely on the properties of [R]. For example:

    - When [R] is an equivalence relation, [quotient] corresponds to
      equivalence classes and the induced ordering is the discrete order.

    - When [R] is a PER the result is similar, but if an "ill-defined"
      element exists, there is one extra value which captures all such
      elements, which is placed below all other values.

    - When [R] is a preorder, then [quotient] is the induced partial order:
      elements are identified up to the symmetric interior of [R].

    - Finally, when [R] is [@eq X], the quotient set contains essentially
      the same elements as the type [X]. However, the quotient set is
      non-constructive, in the sense that an "equivalence class" of [eq]
      can be obtained by giving a defining property for some element of [X]
      and showing (non-constructively) that there exists a unique value
      which satisfies that property.

  Below I attempt to formalize the corresponding properties
  in a fine-grained manner. *)

(** Every element in the quotient set is obtained as the equivalence
  class of an element of [A]. *)

Lemma eqcl_surjective {A B} (R : rel A B) (x : quotient R) :
  exists a, x = eqcl R a.
Proof.
  destruct (in_eqcl_wf x) as [a Ha]. exists a.
  apply antisymmetry; firstorder.
Qed.

Section EQCL_PROPERTIES.
  Context {A} (R : relation A).

  (** If [R] is transitive, then the principal downsets associated
    with related elements are ordered accordingly. *)

  Global Instance eqcl_le `{HR : !Transitive R} :
    Monotonic (eqcl R) (R ++> qle).
  Proof.
    intros u v Huv a. cbn. intro. rauto.
  Qed.

  (** If [R] is a PER, then related elements become equal. *)

  Global Instance eqcl_eq `{HR : !PER R} :
    Monotonic (eqcl R) (R ++> eq).
  Proof.
    intros u v Huv.
    apply antisymmetry; rauto.
  Qed.

  (** If [R] is reflexive, only related elements can become ordered. *)

  Theorem eqcl_reflection `{HR : !Reflexive R} :
    forall x y, qle (eqcl R x) (eqcl R y) -> R x y.
  Proof.
    firstorder.
  Qed.
End EQCL_PROPERTIES.

