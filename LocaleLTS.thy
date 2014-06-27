theory LocaleLTS

imports Main

begin

section {* Labeled transition systems *}

text {* The semantics of a B component is a discrete, eventful, state-transition systems. We 
formalize such systems. First, the notion of labeled \emph{transition} is specified. A transition
has source and destination state, and is labeled by an event. The type for states and events
is left abstract for now, and we thus define a parametric record type:*}

record ('st, 'ev) Transition =
  src :: 'st
  dst :: 'st
  lbl :: 'ev

text {* Next we specify a \emph{labeled transition system}. Such system is fully defined
by a set of initial states, and a set of transitions: *}

record ('st, 'ev) LTS =
  init :: "'st set"
  trans :: "('st, 'ev) Transition set"
  
locale LTS =
fixes
  lts :: "('st, 'ev) LTS"
begin

text {* The (reachable) \emph{states} of a LTS are defined inductively, as follows. *}

  inductive_set states :: "'st set" where
      base[elim!]: "s \<in> init lts \<Longrightarrow> s \<in> states"
    | step[elim!]: "\<lbrakk> t \<in> trans lts; src t \<in> states \<rbrakk> \<Longrightarrow> dst t \<in> states"

  definition successors :: "'st set \<Rightarrow> 'st set" where
    "successors S \<equiv> { s | s . \<exists> t \<in> trans lts . src t \<in> S \<and> dst t = s}"
  
  lemma reachable_init: "init lts \<subseteq> states" by auto

  lemma reachable_stable: "successors states \<subseteq> states"
    unfolding successors_def by auto

text {* The following lemma is useful to identify sufficient conditions to establish 
safety properties. Consider a property that is satisfied by some set of states $S$. If the initial 
states are in $S$, and if the successors of $S$ are in $S$ then all the reachable states are in 
$S$: *}

  lemma reachable_induct_set:
    assumes base: "init lts \<subseteq> S" and step: "successors S \<subseteq> S"
    shows "states \<subseteq> S"
  proof
    fix x
    assume "x \<in> states"
    thus "x \<in> S"
    proof (induct x)
      fix i
      assume "i \<in> init lts"
      with base show "i \<in> S" ..
    next
      fix t
      assume "t \<in> trans lts" "src t \<in> states" "src t \<in> S"
      with step show "dst t \<in> S" unfolding successors_def by auto
    qed
  qed

text {* Next we enunciate and prove a similar lemma for predicates. *}

lemma reachable_induct_predicate:
  assumes base: "\<forall> s \<in> init lts . p s" and 
          step: "\<forall> t \<in> trans lts . p (src t) \<longrightarrow> p (dst t)"
  shows "\<forall> s \<in> states . p s"
proof
  fix x
  assume "x \<in> states" 
  thus "p x"
  proof (induct x)
    fix i
    assume "i \<in> init lts"
    with base show "p i" ..
  next
    fix t
    assume "t \<in> trans lts" "src t \<in> states" "p (src t)"
    with step show "p (dst t)" unfolding successors_def by auto
  qed
qed

subsection {* Behavior *}

text {* Internal behavior. *}

  inductive_set runs :: "('st, 'ev) Transition list set" where
      base: "[] : runs"
    | one[elim!]: "\<lbrakk> t \<in> trans lts; src t \<in> init lts \<rbrakk> \<Longrightarrow> [t] \<in> runs"
    | step[elim!]: "\<lbrakk> t \<in> trans lts; r \<in> runs; r \<noteq> []; src t = dst (last r) \<rbrakk> \<Longrightarrow> r @ [t] \<in> runs"

text {* External behavior. *}

  definition traces :: "'ev list set" where
    "traces \<equiv> { map lbl r | r . r \<in> runs }"

end

end
