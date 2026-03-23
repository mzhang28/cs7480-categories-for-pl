#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/theorion:0.4.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/biceps:0.0.1": *
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/wordometer:0.1.5": word-count, total-words
#import "@preview/cetz:0.4.2": draw

#show: word-count

#show: shorthands.with(
  ($|-$, math.tack),
  ($|=$, math.tack.double),
)
#import cosmos.rainbow: *
#show: show-theorion
// #set par.line(numbering: it => text(fill: gray, [#it]))
#set page(numbering: "1 of 1")
#set heading(numbering: "1.1.1.1")
#set math.equation(numbering: "(1)")
#show link: this => underline(text(this, fill: blue))

#set page(width: 8.5in, height: 11in)
// #set page(width: 8.5in, height: 205in)
// #set page(margin: (right: 3.0in))

#let opp(x) = $#x^sans("op")$
#let fwd = $sans("fwd")$
#let bwd = $sans("bwd")$
#let Set = $bold("Set")$
#let FinSet = $bold("FinSet")$
#let Hom = $bold("Hom")$
#let CC = $cal(C)$
#let PP = $cal(P)$
#let natrec = $sans("natrec")$
#let id = $sans("id")$
#let rev = $sans("rev")$
#let inl = $sans("inl")$
#let inr = $sans("inr")$
#let inv = $sans("inv")$
#let Ob = $sans("Ob")$
#let head = $sans("head")$
#let Prop = $sans("Prop")$
#let tail = $sans("tail")$
#let fst = $sans("fst")$
#let snd = $sans("snd")$
#let KK = $bold(sans("K"))$
#let DA = $sans("DA")$
#let oDA = $sans("oDA")$
#let mDA = $sans("mDA")$
#let rDA = $sans("rDA")$
#let Init = $sans("Init")$
#let Term = $sans("Term")$
#let TODO = text(fill: red, $bold(sans("TODO"))$)

#let (exercise-counter, exercise-box, exercise, show-exercise) = make-frame(
  "exercise",
  "Exercise",
  counter: none,
  inherited-levels: 2,
  inherited-from: heading,
  render: (prefix: none, title: "", full-title: auto, body) => [#strong[#full-title.]#sym.space#emph(body)],
)
#show: show-exercise

#align(center, [
  #heading(numbering: none, text(size: 1.5em)[Algebras and automata])

  Michael Zhang
])



= Automata


Putting these together, we can finally define what a minimal automaton is:

#definition(title: [Minimal automaton])[
  An automaton $Q$ is *minimal* if it is both #link(<reachableAutomaton>)[reachable] and #link(<observableAutomaton>)[observable].
] <minimalAutomaton>

The reachability property enforces that no states can be deleted, and the observability property enforces that no states can be merged, at least without changing the language being recognized.
These are the only two ways to reduce an automaton without changing the language.
This claim could be justified by the fact that the definition of minimization used above coincides with the minimization definition for a coalgebra defined through epi-mono factorization @bezhanishviliMinimizationDuality2012.

On the computation side of things, reachability is pretty trivial to compute algorithmically -- just traverse the state machine and grab all the states visited.
On the other hand, observability requires quotienting by equivalence classes of a hard-to-compute property of basically _every_ state.
In practice, algorithms such as Hopcroft's algorithm optimize this by incrementally comparing states and quotienting as you go.

== Reversing automata

The crux of Brzozowski's minimization algorithm involves reversing the automaton.
The intuition here is, if reachability is more straightforward, we should aim to do it.
Then, we can find some dualization property that allows us to somehow transfer reachability of an automaton into observability of the reverse language, and then use reachability _again_ to get both desired properties on the same language.

The actual reversal process amounts to reversing the arrows of the transition map, as well as exchanging the initial and final states.
Note that normally, when you do this to a deterministic automaton, it becomes a _non-deterministic_ one.
This is because there could be multiple final states, but only one initial state.
When you reverse it, you have a number of initial states.
The algorithm requires that you then make the non-deterministic automaton deterministic, through the powerset construction.

We'll explore a construction which combines the reversing and powersetting in one go.
First off, consider what the shape of output we want is, since this will guide our type-checking as we hone in towards a solution.
We are starting off with a category $DA_LL$ of deterministic automata, and we are trying to get some way of taking each object and obtaining the reverse automata.

Notice that the reverse automata will necessarily recognize the reverse language.
So the output will be an automaton which recognizes $rev(LL)$, in other words an object in $DA_rev(LL)$!
This makes it necessary for us to provide a _functor_ with this signature:

$ DA_LL -> DA_rev(LL) $

As always, we need to find a functor, because the rules governing morphisms will restrict the way the objects can even be mapped to only well-behaved maps.
Otherwise, we could produce some degenerate maps.
This will also give us more benefits, as we will see later.

Time to define action on objects.
For some arbitrary object $Q in DA_LL$, we'd like to produce the reverse automaton.
We can start with what we expect $delta_Q'$, the $delta$ of the transformed automaton to be.
It should be some sort of reversing function, so we should be taking the pre-image of $delta_Q$:

$ delta_Q' :equiv (q, s) mapsto {q' in Q | delta(q', s) = q} $

But this doesn't type-check.
The result is a set, since multiple $q'$s could map to the same $q$ under the old $delta$.
This means our state space fundamentally needs to be a powerset of $Q$.
In that case, $delta_Q'$'s type would need to be $PP(Q) times Sigma -> PP(Q)$.
We can update the function to look like this:

$ delta_Q' :equiv (q, s) mapsto {q' in Q | delta(q', s) in q} $ <preImageDelta>

We can essentially fill in the rest of the definitions now:

- $Q'$'s state space is $PP(Q)$
- $delta_Q'$ was defined above
- $i_Q'$ is the set containing all the final states in $Q$
- $F_Q'$ is the set containing the initial state in $Q$

Here is where the magic happens.
The function $delta_Q$ is essentially a function over sets.
Even though it's doing $Q times Sigma -> Q$, this is equivalent to $Q -> (Sigma -> Q)$, which is $Q -> Q^Sigma$.
Over in our reverse language, we have $delta_Q'$ having type $PP(Q) times Sigma -> PP(Q)$, which is the same as $PP(Q) -> PP(Q)^Sigma$.

*This is exactly the behavior of the contravariant power functor!*

Let's step back one step and build up to this insight.
If we just considered the category of sets $Set$, the _powerset functor_ $PP : Set -> Set$ maps every set $X$ to its power set $PP(X)$.
In particular, for morphisms, it has type $PP(X ->^f Y) : PP(X) -> PP(Y)$.
For any subset of $X$, it maps $f$ restricted to that subset to obtain an image that is in the subset of $Y$.

There is also a contravariant version, which we will denote $PP^* : opp(Set) -> Set$.
In particular, the action on morphisms has type $PP^* (X ->^f Y) : PP(Y) -> PP(X)$.
This action maps a subset of $Y$ into the _pre-image_ under $f$, which is a subset of $X$.

This is exactly what our $delta_Q'$ is doing!
In essence, our desired transformation is performing the covariant powerset functor on each of the components of the automata.
We can concretize this idea by constructing a forgetful functor $U : DA_LL -> Set$ which simply takes the set of states and forgets all the other structure.
Then, we can see clearly that:

$ U(Q) ->^PP^* U(Q') $

Here we introduce a powerful property of the contravariant powerset functor:

#lemma[The contravariant powerset functor $PP^*$ is left adjoint to its own opposite functor $opp(PP^*)$.] <contrPowerSetSelfDual>

#proof[
  The contravariant powerset functor is $PP^* : opp(Set) -> Set$.
  Its opposite functor would be $opp(PP^*) : Set -> opp(Set)$.
  This amounts to showing that for any $X, Y in Set$:

  $ Hom_(Set) (PP^* (X), Y) &tilde.equiv Hom_Set (X, opp(PP^*)(Y)) \ 
  Hom_Set (Y, PP^*(X)) &tilde.equiv Hom_Set (X, opp(PP^*)(Y))
  $

  and really, both $PP^*$ and $op(PP^*)$ have the same action on sets, which is to turn them into their power sets. So really, we are trying to show:

  $ Hom(Y, PP(X)) &tilde.equiv Hom(X, PP(Y)) $

  We can show this via creating a bijection.
  First, the forward direction: define $fwd : Hom(Y, PP(X)) -> Hom(X, PP(Y))$ with the function $lambda (f : Y -> PP(X)) . lambda (x : X) . {y in Y | x in f(y)}$.
  #footnote[Sorry about the sudden lambda notation, I needed to see the type of the argument inline for a second...]
  
  Then, define the inverse direction $bwd : Hom(X, PP(Y)) -> Hom(Y, PP(X))$ with the function $lambda (g : X -> PP(Y)) . lambda (y : Y) . {x in X | y in g(x)}$.

  It's easily to show the inverses compose to the identity:

  $ forall f . " " f & = bwd(fwd(f)) \ 
  & = lambda (y : Y) . {x in X | y in fwd(f)(x) } \
  & = lambda (y : Y) . {x in X | y in (lambda (x : X) . { y in Y | x in f(y)})(x) } \
  & = lambda (y : Y) . {x in X | y in { y in Y | x in f(y) } } \
  & = lambda (y : Y) . {x in X | x in f(y) } } \
  & = lambda (y : Y) . f(y) } } \
  & = f \
  $

  and the other way:

  $ forall g . " " g &= fwd(bwd(g)) \
  & = lambda (x : X) . {y in Y | x in bwd(g)(y) } \
  & = lambda (x : X) . {y in Y | x in (lambda (y : Y) . {x in X | y in g(x) })(y) } \
  & = lambda (x : X) . {y in Y | x in {x in X | y in g(x) } } \
  & = lambda (x : X) . {y in Y | y in g(x) } \
  & = lambda (x : X) . g(x) \
  & = g \
  $
]

@contrPowerSetSelfDual is essentially saying that the contravariant powerset functor is self-dual.
The strategy now is: if we can somehow lift this self-duality into $DA_LL$, we will be able to get an operation that turns reachable automata into observable automata and vice versa.

#let F2 = $overline(2)$

We will devise a functor called $F2$, which is self-dual, that makes this diagram commute:

#align(center, diagram($
  DA_LL
  edge("-->", F2, label-side: #left, bend: #(15deg))
  edge(stroke: #0pt, tack.t, label-side: #center)
  edge("<--", opp(F2), label-side: #right, bend: #(-15deg))
  edge("d", "->", U)
  & opp(DA_rev(LL)) edge("d", "->", U, label-side: #left) \
  Set
  edge("->", PP^*, label-side: #left, bend: #(15deg))
  edge(stroke: #0pt, tack.t, label-side: #center)
  edge("<-", opp(PP^*), label-side: #right, bend: #(-15deg))
  & opp(Set)
$))

This essentially lifts the self-duality of $PP^*$ into $DA_LL$.
The paper @bonchiAlgebracoalgebraDualityBrzozowskis2014 notes that this lifting is true generically

#definition(title: [Self-dual powerset functor lift])[
  Define the functor $F2 : DA_LL -> opp(DA_rev(LL))$ as:

  - action on objects: $F2(Q)$ applies the contravariant powerset functor to all components of the automaton:
    - $Q$ is transformed into the power set of states $PP(Q)$
    - $delta_Q$ is transformed into the pre-image map as described in @preImageDelta. Note that this recognizes the reverse language.
    - $i_Q$ is transformed into the set of all final states
    - $F_Q$ is transformed into the set of all initial states
  - action on morphisms maps a morphism $Q_1 ->^f Q_2$ to its inverse mapping $PP(Q_2) ->^(overline(PP)(f)) PP(Q_1)$
] <F2Def>

#proof[ 
  Omitting for brevity.
  See #cite(<bonchiAlgebracoalgebraDualityBrzozowskis2014>, supplement: [Proposition 9.1]) for the full proof.
]

== (Co-)reflective subcategories

In order to see how all of this machinery comes together, we will introduce some subcategories of $DA_LL$:
- $rDA_LL$ is the category of _only_ reachable automata in $DA_LL$
- $oDA_LL$ is the category of _only_ observable automata in $DA_LL$
- $mDA_LL$ is the category of _only_ minimal automata in $DA_LL$

Since minimal automata are ones that are both reachable and observable, it must also be true that $mDA_LL$ is a subcategory of both $rDA_LL$ and $oDA_LL$.
This means the subcategory relationships can be represented as a sort of diamond diagram:

#align(center, diagram($
& DA_LL
edge("dl", "<-hook")
edge("dr", "<-hook") \
rDA_LL edge("dr", "<-hook") & & oDA_LL edge("dl", "<-hook") \
& mDA_LL
$))

The arrows between them represent inclusion functors.
In fact, these are a special kind of subcategory known as a _reflective_ (and _co-reflective_) subcategory.
For reflective subcategories, this means that the inclusion functor has a left adjoint.
Dually, for co-reflective subcategories, this means that the inclusion functor has a right adjoint.
Let us see why this holds.

#theorem[$rDA_LL$ is a co-reflective subcategory of $DA_LL$. In other words, supposing $I : rDA_LL arrow.r.hook DA_LL$ is the inclusion functor, there exists a functor $R : DA_LL -> rDA_LL$ such that $ I tack.l R $] <rDALCoreflectiveSubcategory>

#proof[
  // #TODO
  // Following @jiri_adamek_abstract_2009.
  For our action on objects, assume we are dealing with an object $Q : DA_LL$.
  We are looking to construct a functor $R$ that is right-adjoint to $I$.

  #let eps = $epsilon.alt$
  
  To do this, we must first define $R$, then construct a unit $eta : id_rDA_LL => R compose I$ and a counit $eps : I compose R => id_DA_LL$ that satisfies the triangle inequalities below.
  Since we are looking for a functor that takes an automaton with possibly unreachable states into its closest reachable approximation, the most obvious thing to do is simply discarding all unreachable states.
  Using the machinery we used above to define reachability, we can say that $R(Q)$ takes the codomain of the morphism $Init -> Q$.
  Thus, $R$ is obviously reachable, and lies in $rDA_LL$.

  Next, define the unit: for some $Q' : rDA_LL$, we must define $eta_Q' : Q' -> R(I(Q'))$.
  We can define this as the _identity_ morphism, since this round trip is a no-op both ways.

  For the counit, for some $Q : DA_LL$, we must define $eps_Q : I(R(Q)) -> Q$.
  Since $R(Q)$ contains the subset of $Q$'s states that are reachable, it's actually a subset.
  So $eps_Q$ can just be a subset inclusion (notice that unlike above, $I(R(Q))$ may be a different object than just $Q$).
  
  Let's check that our definitions for unit and counit satisfy the triangle identities:

  #align(center, table(
    columns: (auto, auto),
    stroke: none,
    column-gutter: 3em,
    
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJJIl0sWzEsMCwiSSBSIEkiXSxbMSwxLCJJIl0sWzAsMSwiSSBldGEiLDAseyJsZXZlbCI6Mn1dLFsxLDIsImVwc2lsb24uYWx0IEkiLDAseyJsZXZlbCI6Mn1dLFswLDIsIjFfSSIsMix7ImxldmVsIjoyfV1d
    align(center, diagram({
    	node((0, 0), [$I$])
    	node((1, 0), [$I R I$])
    	node((1, 1), [$I$])
    	edge((0, 0), (1, 0), [$I eta$], label-side: left, "=>")
    	edge((1, 0), (1, 1), [$epsilon.alt I$], label-side: left, "=>")
    	edge((0, 0), (1, 1), [$1_I$], label-side: right, "=>")
    })),
  
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJSIl0sWzEsMCwiUiBJIFIiXSxbMSwxLCJSIl0sWzAsMSwiUiBldGEiLDAseyJsZXZlbCI6Mn1dLFsxLDIsImVwc2lsb24uYWx0IFIiLDAseyJsZXZlbCI6Mn1dLFswLDIsIjFfUiIsMix7ImxldmVsIjoyfV1d
    align(center, diagram({
    	node((0, -1), [$R$])
    	node((1, -1), [$R I R$])
    	node((1, 0), [$R$])
    	edge((0, -1), (1, -1), [$R eta$], label-side: left, "=>")
    	edge((1, -1), (1, 0), [$epsilon.alt R$], label-side: left, "=>")
    	edge((0, -1), (1, 0), [$1_R$], label-side: right, "=>")
    }))
  ))

  For the first triangle, we can write this equationally as:

  $ eps I compose I eta = 1_I $

  Instantiating this with our $Q' : rDA_LL$:

  $ (eps I)_Q' compose (I eta)_Q' &= (1_I)_Q' \
  I(Q') -->^((I eta)_Q') I(R(I(Q'))) -->^((eps I)_Q') I(Q') &= I(Q') -->^((1_I)_Q') I(Q')
  $

  Well, we have defined $eta$ to be a no-op, so the left side $(I eta)_Q'$ is the identity.
  Since $eps$ is a subset inclusion, for reachable automata, $(eps I)_Q'$ is _also_ the identity.
  Thus, identity compose identity is the identity.

  For the second triangle, we can write this equationally as:

  $ eps R compose R eta = 1_R $

  Instantiating this with $Q : DA_LL$:
  
  $
  (eps R)_Q compose (R eta)_Q = (1_R)_Q \
  R(Q) -->^((R eta)_Q) R(I(R(Q))) -->^((eps R)_Q) R(Q) = R(Q) -->^((1_R)_Q) R(Q)
  $

  Again, we have $eta$ is a no-op, so the left side is the identity.
  The right side goes from reachable to reachable, so the subset inclusion $eps$ is simply restricted to the identity by default here.

  Both triangle inequalities check out, so our adjunction is defined.

  
  // In other words, we are looking for a $Q' : rDA_LL$ such that there are morphisms $f : I(Q') -> Q$ and $g : Q' -> R(Q)$ that obeys the following commutative diagram in $DA_LL$:

  // #align(center, diagram($
  //   I(Q') edge("d", "->", I(g))
  //   edge("dr", "->", f) \
  //   I(R(Q)) edge("->", epsilon.alt_Q, label-side: #right) & Q
  // $))

  // or equationally:

  // $ epsilon.alt_Q compose I(g) = f $

  // where $epsilon.alt : I compose R => id_DA_LL$ is the counit of the adjunction.

  // Let's sketch out what $R$ should look like.
  // Essentially, to go from $DA_LL$ to $rDA_LL$, we want to find the closest approximation of $Q$ inside $rDA_LL$.
  // Well, if there are unreachable states inside our automaton, we would like to discard those states.
  // To reuse machinery we have already constructed, we can define $R$'s action on objects $Q$ by taking the codomain of the morphism $Init -> Q$.
  // By definition, then, $R(Q)$ is reachable.

  // Next, we should define the elements of the adjunction, starting with $epsilon.alt_Q : I(R(Q)) -> Q$, the counit.
  // Since $I(R(Q))$ is a subset of the states in $Q$, this morphism is actually a subset inclusion.
  // Then, 
]

Similarly, for $oDA_LL$:

#theorem[$oDA_LL$ is a reflective subcategory of $DA_LL$. In other words, supposing $I : oDA_LL arrow.r.hook DA_LL$ is the inclusion functor, there exists a functor $Omicron : DA_LL -> oDA_LL$ such that $ O tack.l I $] <oDALReflectiveSubcategory>

#exercise[Prove @oDALReflectiveSubcategory. The proof should look mostly like a dualization of the proof of @rDALCoreflectiveSubcategory.]

The corresponding adjoint functor for $rDA_LL$, called $R$, then restricts automata in the input category to their reachable subset.
Similarly, the corresponding adjoint functor for $oDA_LL$, called $O$, restricts automata in _its_ input category to their observable subset.
And then at the bottom, $mDA_LL$ is both a reflective subcategory and co-reflective subcategory of $oDA_LL$ and $rDA_LL$, respectively.
Let us update the diamond diagram to see these new functors:

#align(center, diagram(spacing: (1.5cm, 2cm), {
  let shift = 2pt
  let obend = 30deg
  let ibend = 15deg
  let tbend = 10deg
// & DA_LL
node((0, -1), name: <DAL>, $DA_LL$)
node((-1, 0), name: <rDAL>, $rDA_LL$)
node((1, 0), name: <oDAL>, $oDA_LL$)
node((0, 1), name: <mDAL>, $mDA_LL$)

edge(<rDAL>, <DAL>, "hook->", shift: shift, bend: obend)
edge(<rDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<DAL>, <rDAL>, "->", shift: shift, bend: ibend, $R$)

edge(<oDAL>, <DAL>, "hook->", shift: -shift, bend: -obend)
edge(<oDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<DAL>, <oDAL>, "->", shift: -shift, bend: -ibend, $O$)

edge(<mDAL>, <rDAL>, "hook->", shift: -shift, bend: -ibend)
edge(<rDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<rDAL>, <mDAL>, "->", shift: -shift, bend: -obend, $O$)

edge(<mDAL>, <oDAL>, "hook->", shift: shift, bend: ibend)
edge(<oDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<oDAL>, <mDAL>, "->", shift: shift, bend: obend, $R$)
}))

Finally, due to our self-dual functor $F2$, we have a functor between $rDA_LL$ and $oDA_LL$, that reflects reachable automata into observable automata in the _reverse_ language:
Thus, our final minimization morphism is simply a concatenation of a series of functors:


#align(center, diagram(spacing: (1cm, 1.5cm),
  edge-stroke: gray,
  {
    
  let shift = 2pt
  let obend = 30deg
  let ibend = 15deg
  let tbend = 10deg
  
node((-2, -1), name: <DAL>, rect($DA_LL$))
node((-3, 0), name: <rDAL>, $rDA_LL$)
node((-1, 0), name: <oDAL>, $oDA_LL$)
node((-2, 1), name: <mDAL>, rect($mDA_LL$))

edge(<rDAL>, <DAL>, "hook->", shift: shift, bend: obend)
edge(<rDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<DAL>, <rDAL>, "->", shift: shift, bend: ibend, text(fill: red, $R$), stroke: 2pt + red)

edge(<oDAL>, <DAL>, "hook->", shift: -shift, bend: -obend)
edge(<oDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<DAL>, <oDAL>, "->", shift: -shift, bend: -ibend, $O$)

edge(<mDAL>, <rDAL>, "hook->", shift: -shift, bend: -ibend)
edge(<rDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<rDAL>, <mDAL>, "->", shift: -shift, bend: -obend, $O$)

edge(<mDAL>, <oDAL>, "hook->", shift: shift, bend: ibend)
edge(<oDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<oDAL>, <mDAL>, "->", shift: shift, bend: obend, $R$)


node((2, -1), name: <DAL2>, $opp(DA_rev(LL))$)
node((1, 0), name: <rDAL2>, $opp(rDA_rev(LL))$)
node((3, 0), name: <oDAL2>, $opp(oDA_rev(LL))$)
node((2, 1), name: <mDAL2>, $opp(mDA_rev(LL))$)

edge(<rDAL2>, <DAL2>, "hook->", shift: shift, bend: obend)
edge(<rDAL2>, <DAL2>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<DAL2>, <rDAL2>, "->", shift: shift, bend: ibend, $opp(R)$)

edge(<oDAL2>, <DAL2>, "hook->", shift: -shift, bend: -obend)
edge(<oDAL2>, <DAL2>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<DAL2>, <oDAL2>, "->", shift: -shift, bend: -ibend, $opp(O)$)

edge(<mDAL2>, <rDAL2>, "hook->", shift: -shift, bend: -ibend)
edge(<rDAL2>, <mDAL2>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<rDAL2>, <mDAL2>, "->", shift: -shift, bend: -obend, $opp(O)$)

edge(<mDAL2>, <oDAL2>, "hook->", shift: shift, bend: ibend)
edge(<oDAL2>, <mDAL2>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<oDAL2>, <mDAL2>, "->", shift: shift, bend: obend, text(fill: red, $opp(R)$), stroke: 2pt + red)

edge(<rDAL>, <oDAL2>, "->", stroke: 2pt + red, bend: 5deg, text(fill: red, $F2$))
edge(<mDAL2>, <mDAL>, "->", stroke: 2pt + red, bend: 5deg, text(fill: red, $opp(F2)$))
}))

#theorem(title: [Brzozowski minimization algorithm])[
  The functor:
  $ (opp(F2) compose opp(R) compose F2 compose R) : DA_LL -> mDA_LL $
  minimizes deterministic automata.
]

#proof[
Due to the way the functors were constructed, we get the following two properties "for free" (ignoring all the work that went into constructing the functors):
- the series of functors preserves the language being recognized (notice the subscript $LL$)
- the resulting automaton is minimal (by definition of $mDA_LL$)

Thus, the theorem holds by construction.
]

= Exercises

Here is a table of some of the exercises that have been distributed throughout the explainer.

#outline(title: none, target: figure.where(kind: "exercise"))

#bibliography("zotero.bib", style: "chicago-author-date")