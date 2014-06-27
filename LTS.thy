theory LTS

imports Main

begin

section {* Labelled transition systems *}

text {* The semantics of a B component is a discrete, eventful, state-transition systems. We 
first define what is meant exactly by such systems. Any system is, at a given time in a state. 
Conversely, a system has a set of possible states. A system evolves from state to state,
and such changes called transitions. Also when a system makes a transition, this is observable
and this observation is called an event. State, transition and event are three different
entities and a type is declared for each: *}

record ('st, 'ev) Transition =
  src :: 'st
  dst :: 'st
  lbl :: 'ev
  
record ('st, 'ev) LTS =
  init :: "'st set" (* a set of initial states *)
  trans :: "('st, 'ev) Transition set" (* a set of transitions *)
  
inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" for m :: "('st, 'ev) LTS" where
  base[elim!]: "s \<in> init m \<Longrightarrow> s \<in> states m"
| step[elim!]: "\<lbrakk> t \<in> trans m; src t \<in> states m \<rbrakk> \<Longrightarrow> dst t \<in> states m"
  
definition successors :: "('st, 'ev) LTS \<Rightarrow> 'st set \<Rightarrow> 'st set" where
"successors lts S \<equiv> { s | s . \<exists> t \<in> trans lts. src t \<in> S \<and> dst t = s}"
  
text {* A few lemmas related to reachable states are then enunciated and proved. 
First, all the initial states are reachable states:*}

lemma reachable_init: "init m \<subseteq> states m" 
  by auto

lemma reachable_stable: "successors m (states m) \<subseteq> states m"
  unfolding successors_def by auto
  
text {* The following lemma is related to the identification of sufficient conditions to establish 
safety properties. Consider a property that is satisfied by some set of states $S$. If the initial 
states are in $S$, and if the successors of $S$ are in $S$ then all the reachable states are in 
$S$. *}

lemma reachable_induct_set:
  assumes base: "init m \<subseteq> S" and step: "successors m S \<subseteq> S"
  shows "(states m) \<subseteq> S"
proof
  fix x
  assume "x \<in> states m"
  thus "x \<in> S"
  proof (induct x)
    fix i
    assume "i \<in> init m"
    with base show "i \<in> S" ..
  next
    fix t
    assume "t \<in> trans m" "src t \<in> states m" "src t \<in> S"
    with step show "dst t \<in> S" unfolding successors_def by auto
  qed
qed

text {* Next we enunciate and prove a similar lemma for predicates. *}
lemma reachable_induct_predicate:
  assumes base: "\<forall> s \<in> init m . p s" and 
          step: "\<forall> t \<in> trans m . p (src t) \<longrightarrow> p (dst t)"
  shows "\<forall> s \<in> (states m) . p s"
proof
  fix x
  assume "x \<in> states m" 
  thus "p x"
  proof (induct x)
    fix i
    assume "i \<in> init m"
    with base show "p i" ..
  next
    fix t
    assume "t \<in> trans m" "src t \<in> states m" "p (src t)"
    with step show "p (dst t)" unfolding successors_def by auto
  qed
qed

subsection {* Behavior *}

text {* Internal behavior. *}

inductive_set runs :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Transition list set"  
          for m :: "('st, 'ev) LTS" where
  base: "[] : runs m"
| one[elim!]: "\<lbrakk> t \<in> trans m; src t \<in> init m \<rbrakk> \<Longrightarrow> [t] \<in> runs m"
| step[elim!]: "\<lbrakk> t \<in> trans m; r \<in> runs m; r \<noteq> []; src t = dst (last r) \<rbrakk> \<Longrightarrow> r @ [t] \<in> runs m"

text {* External behavior. *}

definition traces :: "('st, 'ev) LTS \<Rightarrow> 'ev list set" where
  "traces m \<equiv> { map lbl r | r . r \<in> runs m }"

end


