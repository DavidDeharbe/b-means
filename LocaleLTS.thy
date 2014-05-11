theory LocaleLTS

imports Main

begin

section {* Labelled transition systems *}

text {* The semantics of a B component is a discrete, eventful, state-transition systems. We 
first define what is meant exactly by such systems. Any system is, at a given time in a state. 
Conversely, a system has a set of possible states. A system evolves from state to state,
and such changes called transitions. Also when a system makes a transition, this is observable
and this observation is called an event. State, transition and event are three different
entities and a type is declared for each: *}

locale Transition =
fixes 
  src :: "'trans \<Rightarrow> 'state" and
  dst :: "'trans \<Rightarrow> 'state" and
  evt :: "'trans \<Rightarrow> 'event"
  
locale LTS = Transition src dst evt 
for
  src :: "'trans \<Rightarrow> 'state" and
  dst :: "'trans \<Rightarrow> 'state" and
  evt :: "'trans \<Rightarrow> 'event"
+
fixes
  init :: "'state set" and
  trans :: "'trans set"
begin

  inductive_set states :: "'state set" where
      base[elim!]: "s \<in> init \<Longrightarrow> s \<in> states"
    | step[elim!]: "\<lbrakk> t \<in> trans; src t \<in> states \<rbrakk> \<Longrightarrow> dst t \<in> states"

  definition successors :: "'state set \<Rightarrow> 'state set" where
    "successors S \<equiv> { s | s . \<exists> t \<in> trans . src t \<in> S \<and> dst t = s}"
  
  lemma reachable_init: "init \<subseteq> states" by auto

  lemma reachable_stable: "successors states \<subseteq> states"
    unfolding successors_def by auto

text {* The following lemma is related to the identification of sufficient conditions to establish 
safety properties. Consider a property that is satisfied by some set of states $S$. If the initial 
states are in $S$, and if the successors of $S$ are in $S$ then all the reachable states are in 
$S$. *}

  lemma reachable_induct_set:
    assumes base: "init \<subseteq> S" and step: "successors S \<subseteq> S"
    shows "states \<subseteq> S"
  proof
    fix x
    assume "x \<in> states"
    thus "x \<in> S"
    proof (induct x)
      fix i
      assume "i \<in> init"
      with base show "i \<in> S" ..
    next
      fix t
      assume "t \<in> trans" "src t \<in> states" "src t \<in> S"
      with step show "dst t \<in> S" unfolding successors_def by auto
    qed
  qed

text {* Next we enunciate and prove a similar lemma for predicates. *}

lemma reachable_induct_predicate:
  assumes base: "\<forall> s \<in> init . p s" and 
          step: "\<forall> t \<in> trans . p (src t) \<longrightarrow> p (dst t)"
  shows "\<forall> s \<in> states . p s"
proof
  fix x
  assume "x \<in> states" 
  thus "p x"
  proof (induct x)
    fix i
    assume "i \<in> init"
    with base show "p i" ..
  next
    fix t
    assume "t \<in> trans" "src t \<in> states" "p (src t)"
    with step show "p (dst t)" unfolding successors_def by auto
  qed
qed

end

end
