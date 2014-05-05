theory Machine

imports Main Misc

begin

section {* State-transition systems *}

text {* The semantics of a B component is a discrete, eventful, state-transition systems. We 
first define what is meant exactly by such systems. Any system is, at a given time in a state. 
Conversely, a system has a set of possible states. A system evolves from state to state,
and such changes called transitions. Also when a system makes a transition, this is observable
and this observation is called an event. State, transition and event are three different
entities and a type is declared for each: *}

typedecl STATE
typedecl TRANSITION
typedecl EVENT

text {* These different entities are related through the following functions: *}
consts Src :: "TRANSITION \<Rightarrow> STATE"
consts Dst :: "TRANSITION \<Rightarrow> STATE"
consts Evt :: "TRANSITION \<Rightarrow> EVENT"

(* B machines are discrete transition systems. 
   Their are specified as a record type with associated well-definedness conditions. *)

record LTS =
  State :: "STATE set" (* a set of states *)
  Init :: "STATE set" (* a set of initial states *)
  Trans :: "TRANSITION set" (* a set of transitions *)
  
(* Condition 1 : the initial states are in the set of states *)
definition wd_LTS_Init :: "LTS \<Rightarrow> bool" where
"wd_LTS_Init m \<equiv> Init m \<subseteq> State m"

(* Condition 2 : the transition is a relation on the set of states *)
definition wd_LTS_Trans :: "LTS \<Rightarrow> bool" where
"wd_LTS_Trans m \<equiv> \<forall> t . t \<in> Trans m \<longrightarrow> Src t \<in> State m \<longrightarrow> Dst t \<in> State m"

(* A well-defined machine must satisfy both conditions *)

definition wd_LTS :: "LTS \<Rightarrow> bool" where
"wd_LTS m \<equiv> wd_LTS_Init m \<and> wd_LTS_Trans m"

(* To use Isabelle machinery for relations, we define a successor relation *)
definition succ_rel :: "LTS \<Rightarrow> STATE rel" where
"succ_rel m \<equiv> { p. \<exists> t . p = (Src t, Dst t) \<and> t \<in> (Trans m) }"
  
(* To use Isabelle machinery for relations, we define a successor relation *)
definition succ :: "LTS \<Rightarrow> STATE set \<Rightarrow> STATE set" where
"succ m s \<equiv> succ_rel m `` s"
  
(* Then we have the notion of the reachable states of a machine *)
definition reachable :: "LTS \<Rightarrow> STATE set" where
"reachable m \<equiv> lfp(\<lambda> S . Init m \<union> succ m S)"

(* The lambda-term defining the fixpoint is monotonic *)
lemma mono_reachable: "mono( \<lambda>T. Init m \<union> succ m S)" 
proof(rule monoI, blast)
qed

text {* A few lemmas related to reachable states are then enunciated and proved. First, all the initial states are reachable states:*}
lemma reachable_init:
assumes wd: "wd_LTS m" shows "Init m \<subseteq> reachable m"
proof(simp add:reachable_def lfp_def, blast)
qed

text {* Next we have that the successors of any set of reachable states are reachable.*}
lemma reachable_stable:
assumes hyp: "s \<subseteq> reachable m" 
shows "succ m s \<subseteq> reachable m"
proof-
  from assms have 1: "succ m s \<subseteq> succ m (reachable m)" by (simp only:succ_def, blast)
  have "succ m (reachable m) \<subseteq> reachable m"  by (simp only:succ_def reachable_def lfp_def, blast)
  with 1 show "succ m s \<subseteq> reachable m" by blast
qed

text {* The following lemma is related to the identification of sufficient conditions to establish safety properties. Consider
a property that is satisfied by some set of states $S$. If the initial states are in $S$, and if the successors of $S$ are in $S$ then
all the reachable states are in $S$. *}
lemma reachable_induct:
  assumes base: "Init m \<subseteq> S" and step: "succ m S \<subseteq> S"
  shows "(reachable m) \<subseteq> S"
proof-
  from assms have "Init m \<union> succ m S \<subseteq> S" by blast
  hence "lfp (\<lambda> S . Init m \<union> succ m S) \<subseteq> S" by (rule lfp_lowerbound)
  thus "(reachable m) \<subseteq> S" unfolding reachable_def .
qed

text {* The next lemma is similar, but for safety properties expressed as predicates over states instead of sets of states. *}

lemma reachable_induct_pred:
  assumes base: "\<forall> s \<in> Init m . p s" and step: "\<forall> s . p s \<longrightarrow> (\<forall> s' \<in> succ m {s} . p s')"
  shows "\<forall> s \<in> reachable m . p s"
proof -
  let ?S = "{ x | x . p x }"
  from base have 1: "Init m \<subseteq> ?S " by auto
  from step have "\<forall> s \<in> ?S . succ m { s } \<subseteq> ?S" by auto
  then have "\<forall> x . x \<in> succ m ?S \<longrightarrow> x \<in> ?S"
    proof(simp only:succ_def, auto)
    qed
  then have 2: "succ m ?S \<subseteq> ?S" by auto
  from 1 and 2 have "reachable m \<subseteq> ?S" by (simp add:reachable_induct)
  from this show "\<forall>s \<in> reachable m . p s" by auto
qed

section {* B machine *}

text {* A B machine is a state-transition system together with an invariant. An invariant
is a predicate on the states of the system. *}

record MACHINE =
  Lts :: LTS
  Inv :: "STATE \<Rightarrow> bool"
  
text {* A B machine is considered correct when all the reachable states satisfy the
        invariant. *}

definition correct_MACHINE :: "MACHINE \<Rightarrow> bool" where
  "correct_MACHINE m \<equiv> \<forall> s \<in> reachable (Lts m) . (Inv m) s"

text {* The following theorem states two sufficient conditions to establish that a machine is
correct. *}

theorem machine_po:
  assumes poinit: "\<forall> s \<in> Init (Lts m) . (Inv m) s" 
      and postep: "\<forall> s . (Inv m) s \<longrightarrow> (\<forall> s' \<in> succ (Lts m) {s} . (Inv m) s')"
  shows "correct_MACHINE m"
proof-
  from assms have "\<forall>s\<in>reachable (Lts m). (Inv m) s"
    proof(rule reachable_induct_pred[of "Lts m" "Inv m"])
    qed
  then show ?thesis by (simp only:correct_MACHINE_def)
qed

end
