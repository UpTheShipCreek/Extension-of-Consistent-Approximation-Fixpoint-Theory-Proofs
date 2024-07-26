# Extension of Consistent Approximation Fixpoint Theory Proofs
Approximation Fixpoint Theory has a wide range of applications in the context of
logic programming and its approximate fields, such as databases and artificial intelligence.
It gives us a framework for understanding the semantics of non-monotonic logic, a type
logic which closely mirrors human reasoning; deducing from incomplete data and making
assumptions based on the now available information, whilst also being able to retract
those assumptions when new, contradictory, information is presented.  

Non-monotonicity is a concept that appears in various systems. While
this extension of the Approximation Fixpoint Theory spawned from
reasoning about the semantics of logic programs, we can certainly map it
into other fields. It is thus vital to build an intuitive understanding
of the motivation behind the theory, as well as the math itself.  

We can start with our understanding of knowledge. A very basic and
intuitive way to think about knowledge is through sets. A set of
propositions could be thought of as representing our knowledge about a
certain system. In two valued logic, if a proposition of the general
domain is missing from this set, it means that it is false, and vise
versa.

Let's say we know two people, John and Bill. We know nothing about Bill
but we know that John uses Windows 11. Trying to represent this in
traditional logic already proves challenging, since we are basically
forced to assume that Bill doesn't use Windows, which is not necessarily
true.  

Let's also assume that we know that if someone doesn't use Windows, they
are a good person.  

$good(Person) \leftarrow \neg Person(windows)$  

At this point it is important to note, that this is an intensional example
for clarity. In reality, this theory discusses extensional structures,
structures which we should understand as general formulas of deduction.
Those formulas can just as easily be used for numbers or any other
relation. We generally don't need to attribute any specific intensional
property to the above formulation for it to be useful.  

Continuing with this specific example, if we naively try to extract
truth from those rules, we will end up with more truth about Bill than
about John, namely we will end up saying that we know Bill (represented
by the empty set) is a good person while John (represented by the set
with just one element) is not.

$\\{\\} \subseteq \\{windows\\} \Rightarrow good(\\{\\}) = True \geq_{truth} False = good(\\{windows\\})$  

This approach, of course, doesn't correspond to our intuition about
knowledge and truth and yet it is this very approach that is used for
defining the semantics of positive logic programs. It is obvious that we
need a different concept for monotonicity, as well as a different
representation of knowledge if we are to sufficiently reason about more
complex systems.  

The first problem is with the initial modeling; in simple databases and
programs it might be reasonable to assume that Bill doesn't use Windows,
we are basically operating under the presumption that our knowledge is
complete, so if he did, we'd know about it. That's not a reasonable
assumption neither in our everyday lives, nor in more complex systems.  

So, firstly, we can do away with this by adding a third truth value
which we can call \"I don't know\" or simply $Undefined$. With this tool
our example already appears to align better with our intuition; we don't
know if Bill uses Windows or not, so by applying our rule:  

$\\{\\} \subseteq \\{windows\\} \Rightarrow good(\\{\\}) = Undefined \leq False = good(\\{windows\\})$  

We can see that we used a different ordering now, an ordering on which
it doesn't matter if something is simply $True$ or $False$; what
actually matters is whether or not we know about it. We will call this
information ordering. Formally this ordering can be expressed as:  

$Undefined \leq False \wedge Undefined \leq True$  

A problem that we face now, is that we still need the $\leq_{truth}$ ordering. That's
because we need our model to be \"truth minimal\". Intuitively, we know
that we wouldn't want to believe every assertion we can think of so long
as it doesn't contradict any evidence. For example, it generally
wouldn't be reasonable to assume that Bill has an invisible pet dragon
in his house, even though this assertion could probably never contradict
any evidence. So, it is obvious that we still need a way to keep our
models from building towards this excess of assumptions because they are
too \"lazy\" to account for it.  

The way we solve for this is by establishing a bijection between the
functions that can account for the information ordering and our original
naive functions. We can represent the third truth value through the
difference of a pair of naive functions $(f_1, f_2)$. We can of course
reason about these functions as sets:  

$f : D \rightarrow \\{False, True\\}$, then $F$ is a set of element $D$
where:

-   $\forall d \in F, f(d) = True$

-   $\forall d \notin F, f(d) = False$

Or, more concisely:  

$F = \\{(d : D) | f(d) = True\\}$  

If we then have two sets of truths, those two sets are allowed to contradict each
other. What we actually know can be represented as their intersection,
and what we don't know as their difference. Formally, for sets $F_1$ and
$F_2$ representing the $f_1$ and $f_2$ functions respectively, the set
of undefined values of the function $f = (f_1, f_2)$ can be expressed as
$F_2 - F_1$ and the set of the actual knowledge as $F_2 \cap F_1$.  

Note that we take the difference $F_2 - F_1$ rather than $F_1 - F_2$.
That's because this approximation of knowledge relies in the
reconciliation between $F_2$ assuming too much and $F_1$ assuming too
little.  

Marc Denecker, Victor W. Marek, and Mirosław Truszczynskic[[1]](https://www.sciencedirect.com/science/article/pii/S0890540104000306) showed that by iterating a proper
operator, starting from the worst possible pair $(f_1, f_2)$, we can
reach a fixpoint. The contribution of Angelos Charalambidis, Panos
Rondogiannis, and Ioanna Symeonidou[[2]](https://arxiv.org/abs/1804.08335) was to then generalize this approximation structure into higher order
relations, where the functions are not simple predicates, but higher
order predicates, predicates that can handle as input functions of any
complexity. The formalization of the precise inner workings of this
generalization is the subject of this thesis.
