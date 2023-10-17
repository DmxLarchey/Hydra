# Hercules kills the Hydra in less the 300 lines of Coq

## The battle of Hercules and the Hydra
The Hydra is mainly a _Rose tree_, that is a finite tree with arbitrary branching.
Hercules tries to kill the Hydra by chopping of heads (ie leaves of the Hydra) but 
the Hydra responds in growing copies of specific sub-trees determined by which
head was chopped last.

The Hercules and Hydra game consists in Hercules chopping off heads of the Hydra until
the Hydra has no more heads left. In response to a head cut, the Hydra may grow an arbitrary
number of copies of the sub-tree rooted two levels below the head that was last chopped
by Hercules.

_Importantly_ the previous rule excludes root leaves (ie a leaf just above the root of the Hydra).
If Hercules chops a root leaf, then the Hydra cannot morph in response: it must wait for the next 
move of Hercules. Absent of that exclusion, the game would possibly not end because 
nothing would force the number of nodes to (sometimes) decrease after the response of Hydra.

There are variants of the game where the number of copies that the Hydra makes is
determined fully by the advancement of the game (eg the number of head that were 
chopped by Hercules so far) by this does not affect the termination property of the
game.

## The code
This standalone (one file) proof was implemented by Dominique Larchey-Wendling, 
see [`hydra.v`](theories/hydra.v). It is distributed under the terms of the [`MPL-2.0`](LICENSE).

## Rounds vs. moves
In the code of [`hydra.v`](theories/hydra.v), we only model a _round_ which is
the combination of a head cut by Hercules and a conforming response by the Hydra
(see above).
We do not model the moves of Hercules and Hydra independently because:
- while a move of Hercules is nondeterministic and only depends on the current
  shape of the Hydra;
- the response from the Hydra (also possibly nondeterministic), is still
  constrained by which head was chopped off last. The growing of copies of 
  sub-hydras depends on the position of this last chopped head.
  
Modeling this dependency would lengthen the code base because we would need
to represent the position of a head inside the Hydra so that Hercules can
transmit that information. By combining Hercules move and the Hydra's
response into the notion of round, the information can be transmitted 
without requiring external information.

## The Hydra data structures

### Mutual vs. nested: my biased point of view
In this code, we implement hydras as an inductive type _nested_ with lists:
```
Inductive hydra := 
  | hydra_cons : list hydra → hydra.
```
whereas the [Hydra Battles](https://github.com/coq-community/hydra-battles) version favors
a mutual inductive type instead:
```
Inductive Hydra :=
  | Hydra_node  : Hydrae → Hydra
with Hydrae :=
  | Hydrae_nil  : Hydrae
  | Hydrae_cons : Hydra → Hydrae → Hydrae.
```
and we notice that the type `Hydrae` is an isomorphic copy of the type `list Hydra`.

IMHO there is _only one reason_ to favor the mutual version `Hydra`/`Hydrae` over the nested
`hydra`/`list hydra` version: Coq can generate mutual inductive schemes for you and you 
do not have to deal with mutual or nested fixpoints and intricacies the _guard condition_.

On the downside however, the type `Hydrae` is not identical to `list Hydra` and thus
one cannot use all the generic tools of the `List` library. You basically have to
rewrite those of the `List` tools you need. This is really a painful endeavor that unnecessarily 
lengthen the code base. Should you want to define a variant of `Hydra/Hydrae`, eg by
decorating nodes with data, and you get yet _another_ copy of `list _` which 
requires another partial rewriting of the `List` library.

On the other hand, working with the nested types `hydra`/`list hydra` requires you
to master nested fixpoints because Coq (so far) does not generate powerful enough
recursors (ie induction principles) for nested types. But they can be build _by hand_:
- first of all, this is _a good incentive to learn_ working with guarded fixpoints
  directly and how Coq actually builds recursors;
- you can work with `list hydra` using the tools of the `List` library _as they are_;
- the code is now much more succinct and if you need to extend the `List` library,
  your extension can be used elsewhere. Same remark if you extend `hydra` to
  decorated roses trees as eg:
  ```
  Inductive ltree X :=
    | ltree_cons : X → list (ltree X) → ltree X. 
  ``` 
  No need to duplicate everything. 
  
So apart from the initial difficulty of having to understand how the guard condition
works, which is btw something you should do anyway to become fluent in working with inductive
types, there are only advantages with the choice of nesting over mutual.

### The isomorphism
To compare and illustrate the practical differences between the mutual and nested
versions, it is a _very good exercise_ to implement the isomorphism between `hydra`
and `Hydra` in Coq. You will learn how to deal with nested
fixpoints _and_  mutual fixpoints.

This code contains, as an extra educational contribution, the construction of the
isomorphism between `hydra` and `Hydra`:
1. we first represent the isomorphism as an inductive relation. This follows the 
   general approach of the [_Braga method_](https://github.com/DmxLarchey/The-Braga-Method);
2. we then show that this relation is _functional_ and _injective_;
3. we then _realize_ that relation by fully specified functions in
   _both directions_;
4. finally, we show that this gives a functional bijection, and derive convenient
   fixpoint equations for the isomorphism. 


