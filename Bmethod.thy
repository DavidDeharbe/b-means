theory Bmethod

imports Main Misc

begin

section {* B components as state-transition systems *}

text {* We consider states and transitions as basic entities, and declare types for those entities. *}

typedecl STATE
typedecl TRANSITION

(* functions to retrieve the source and destination of a transition *)

consts Src :: "TRANSITION \<Rightarrow> STATE"
consts Dst :: "TRANSITION \<Rightarrow> STATE"

definition Joins :: "TRANSITION \<Rightarrow> (STATE \<times> STATE)" where
  "Joins t \<equiv> (Src t, Dst t)"


(* B machines are discrete transition systems. 
   Their are specified as a record type with associated well-definedness conditions. *)

record MACHINE =
  State :: "STATE set" (* a set of states *)
  Init :: "STATE set" (* a set of initial states *)
  Trans :: "TRANSITION set" (* a set of transitions *)
  
(* Condition 1 : the initial states are in the set of states *)
definition wd_MACHINE_Init :: "MACHINE \<Rightarrow> bool" where
"wd_MACHINE_Init m \<equiv> Init m \<subseteq> State m"

(* Condition 2 : the transition is a binary relation on the set of states *)
definition wd_MACHINE_Trans :: "MACHINE \<Rightarrow> bool" where
"wd_MACHINE_Trans m \<equiv> \<forall> t . t \<in> Trans m \<longrightarrow> Src t \<in> State m \<longrightarrow> Dst t \<in> State m"

(* A well-defined machine must satisfy both conditions *)

definition wd_MACHINE :: "MACHINE \<Rightarrow> bool" where
"wd_MACHINE m \<equiv> wd_MACHINE_Init m \<and> wd_MACHINE_Trans m"

(* To use Isabelle machinery for relations, we define a successor relation *)
definition succ_rel :: "MACHINE \<Rightarrow> STATE rel" where
"succ_rel m \<equiv> { p. \<exists> t . p = (Src t, Dst t) \<and> t \<in> (Trans m) }"
  
(* Then we have the notion of the reachable states of a machine *)
definition reachable :: "MACHINE \<Rightarrow> STATE set" where
"reachable m \<equiv> lfp(\<lambda> S . Init m \<union> (succ_rel m) `` S)"

(* The lambda-term defining the fixpoint is monotonic *)
lemma mono_reachable: "mono( \<lambda>T. Init m \<union> (succ_rel m) `` S)" 
proof(rule monoI, blast)
qed

text {* A few lemmas related to reachable states are then enunciated and proved. First, all the initial states are reachable states:*}
lemma reachable_init:
assumes wd: "wd_MACHINE m" shows "Init m \<subseteq> reachable m"
proof(simp add:reachable_def lfp_def, blast)
qed

text {* Next we have that the successors of any set of reachable states are reachable.*}
lemma reachable_stable:
assumes hyp: "s \<subseteq> reachable m" 
shows "succ_rel m `` s \<subseteq> reachable m"
proof-
  from assms have 1: "succ_rel m `` s \<subseteq> succ_rel m `` reachable m" by (blast)
  have "succ_rel m `` reachable m \<subseteq> reachable m"  by (simp only:reachable_def lfp_def, blast)
  with 1 show "succ_rel m `` s \<subseteq> reachable m" by blast
qed

text {* The following lemma is related to the identification of sufficient conditions to establish safety properties. Consider
a property that is satisfied by some set of states $S$. If the initial states are in $S$, and if the successors of $S$ are in $S$ then
all the reachable states are in $S$. *}
lemma reachable_induct:
  assumes base: "Init m \<subseteq> S" and step: "(succ_rel m) `` S \<subseteq> S"
  shows "(reachable m) \<subseteq> S"
proof-
  from assms have "Init m \<union> succ_rel m `` S \<subseteq> S" by blast
  hence "lfp (\<lambda> S . Init m \<union> succ_rel m `` S) \<subseteq> S" by (rule lfp_lowerbound)
  thus "(reachable m) \<subseteq> S" unfolding reachable_def .
qed

subsection {* Observable behaviour: a set of traces *}

definition traces :: "MACHINE \<Rightarrow> STATE list set" where
"traces m \<equiv> lfp (\<lambda> S . { [s] | s . s \<in> Init m } \<union> { tr @ [s] | tr s . tr \<in> S \<and> (last tr, s) \<in> succ_rel m })"

lemma mono_traces: "mono( \<lambda> S . { [s] | s . s \<in> Init m } \<union> { tr @ [s] | tr s . tr \<in> S \<and> (last tr, s) \<in> succ_rel m })" 
proof(rule monoI, blast)
qed

section {* B refinement: two components glued by a relation between states *}

record REFINEMENT =
  Abstract :: MACHINE
  Concrete :: MACHINE
  Glue :: "STATE rel" (* relates Abstract to Concrete - see wd_REFINEMENT_glue *)
  
definition wd_REFINEMENT_machines :: "REFINEMENT \<Rightarrow> bool" where
"wd_REFINEMENT_machines r \<equiv> 
  wd_MACHINE(Abstract r) \<and> wd_MACHINE(Concrete r)"

definition wd_REFINEMENT_glue :: "REFINEMENT \<Rightarrow> bool" where
"wd_REFINEMENT_glue r \<equiv> Glue r \<subseteq> State (Concrete r) \<times> State (Abstract r)"

definition sound_REFINEMENT_init :: "REFINEMENT \<Rightarrow> bool" where
"sound_REFINEMENT_init r \<equiv> \<forall> s \<in> Init (Concrete r) . \<exists> sa \<in> Init(Abstract r) . (s, sa) \<in> Glue r"

definition sound_REFINEMENT_trans :: "REFINEMENT \<Rightarrow> bool" where
"sound_REFINEMENT_trans r \<equiv> \<forall> tc \<in> Trans (Concrete r) . \<exists> ta \<in> Trans (Abstract r) .
(Src tc, Src ta) \<in> Glue r \<and> (Dst tc, Dst ta) \<in> Glue r" 

definition sound_REFINEMENT :: "REFINEMENT \<Rightarrow> bool" where
"sound_REFINEMENT r \<equiv> sound_REFINEMENT_init r \<and> sound_REFINEMENT_trans r"

text {* A special refinement is one that does not change anything, namely the
identity refinement. It is defined as a function that takes a machine and
returns the identity refinement. *}

definition refinement_id :: "MACHINE \<Rightarrow> REFINEMENT" where
"refinement_id m \<equiv> \<lparr> Abstract = m, Concrete = m, Glue = Id \<rparr>"

text {* We have that the identity refinement is sound. *}

lemma "sound_REFINEMENT(refinement_id m)"
proof(simp add:sound_REFINEMENT_def  
      sound_REFINEMENT_trans_def sound_REFINEMENT_init_def refinement_id_def, auto)
qed

text {* Next, we definement composition of refinements. This is only defined if the
composed refinements have matching set of states, otherwise it is left
undefined. *}

definition refinement_compose :: "REFINEMENT \<Rightarrow> REFINEMENT \<Rightarrow> REFINEMENT option" where
"refinement_compose r1 r2 \<equiv> 
  (if Concrete r1 = Abstract r2 then
    Some \<lparr> Abstract = Abstract r1, Concrete = Concrete r2, Glue = (Glue r2) O (Glue r1)\<rparr>
  else None)"

lemma refinement_compose_soundness:
  assumes 
    "sound_REFINEMENT r1" and "sound_REFINEMENT r2" and
    "refinement_compose r1 r2 = Some r"
  shows "sound_REFINEMENT r"
proof(cases "Concrete r1 = Abstract r2")
  case False
    hence "refinement_compose r1 r2 = None" by (simp add:refinement_compose_def)
    with assms(3)
    have "Some r = None" by simp
    thus ?thesis by simp
next
  def rv \<equiv> "\<lparr> Abstract = Abstract r1, Concrete = Concrete r2, Glue = Glue r2 O Glue r1 \<rparr>"
  case True
    from this have guard : "Concrete r1 = Abstract r2" .
    hence "refinement_compose r1 r2 = Some rv"
    by (simp add:refinement_compose_def rv_def)
    with assms(3)
    have r: "r = rv" by simp
    from assms(2)
    have i2: "sound_REFINEMENT_init r2" by (simp add: sound_REFINEMENT_def)
    from assms(1)
    have i1: "sound_REFINEMENT_init r1" by (simp add: sound_REFINEMENT_def)    
    from i2 and i1
    have i: "sound_REFINEMENT_init rv"
    proof(simp add:sound_REFINEMENT_init_def rv_def)
      have "\<forall>s\<in>Init (Concrete r2). \<exists>sa\<in>Init (Abstract r2). (s, sa) \<in> Glue r2 \<Longrightarrow>
            \<forall>s\<in>Init (Abstract r2). \<exists>sa\<in>Init (Abstract r1). (s, sa) \<in> Glue r1 \<Longrightarrow> 
            \<forall>s\<in>Init (Concrete r2). \<exists>sa\<in>Init (Abstract r1). (s, sa) \<in> Glue r2 O Glue r1"
        by (simp add: relcomp_totality)
      moreover
        with guard have "Init (Concrete r1) = Init (Abstract r2)" by simp
      ultimately
      show "\<forall>s\<in>Init (Concrete r2). \<exists>sa\<in>Init (Abstract r2). (s, sa) \<in> Glue r2 \<Longrightarrow>
            \<forall>s\<in>Init (Concrete r1). \<exists>sa\<in>Init (Abstract r1). (s, sa) \<in> Glue r1 \<Longrightarrow> 
            \<forall>s\<in>Init (Concrete r2). \<exists>sa\<in>Init (Abstract r1). (s, sa) \<in> Glue r2 O Glue r1" by simp
    qed
  moreover  
    from assms(1)
    have t1: "sound_REFINEMENT_trans r1" by (simp add: sound_REFINEMENT_def)
    from assms(2)
    have t2: "sound_REFINEMENT_trans r2" by (simp add: sound_REFINEMENT_def)
    from t1 and t2
    have t: "sound_REFINEMENT_trans rv"
      proof (simp add:sound_REFINEMENT_trans_def rv_def)
        have 
          "\<forall>tc\<in>Trans (Concrete r1). \<exists>ta\<in>Trans (Abstract r1). (Src tc, Src ta) \<in> Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r1 \<Longrightarrow>
           \<forall>tc\<in>Trans (Concrete r2). \<exists>ta\<in>Trans (Concrete r1). (Src tc, Src ta) \<in> Glue r2 \<and> (Dst tc, Dst ta) \<in> Glue r2 \<Longrightarrow>
           \<forall>tc\<in>Trans(Concrete r2). \<exists>ta\<in>Trans(Abstract r1). (Src tc, Src ta) \<in> Glue r2 O Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r2 O Glue r1"
          by (simp add: relcomp_pair)
        moreover
          with guard have "Trans (Concrete r1) = Trans (Abstract r2)" by simp
        ultimately
        show
          "\<forall>tc\<in>Trans (Concrete r1). \<exists>ta\<in>Trans (Abstract r1). (Src tc, Src ta) \<in> Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r1 \<Longrightarrow>
           \<forall>tc\<in>Trans (Concrete r2). \<exists>ta\<in>Trans (Abstract r2). (Src tc, Src ta) \<in> Glue r2 \<and> (Dst tc, Dst ta) \<in> Glue r2 \<Longrightarrow>
           \<forall>tc\<in>Trans(Concrete r2). \<exists>ta\<in>Trans(Abstract r1). (Src tc, Src ta) \<in> Glue r2 O Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r2 O Glue r1"
          by simp
      qed
  ultimately
    have "sound_REFINEMENT rv" 
    by (simp add:sound_REFINEMENT_def)
    with r show "sound_REFINEMENT r" by simp
qed

text {* We now want to verify that our definition of refinement composition satisfies
some simple properties. First any identity refinement is left-neutral: *}

lemma refinement_compose_neutral_left:
  assumes "sound_REFINEMENT r"
  shows "Abstract r = m \<Longrightarrow> refinement_compose (refinement_id m) r = Some r"
proof(simp add:sound_REFINEMENT_def refinement_compose_def refinement_id_def)
qed

text {* Second, any identity refinement is right-neutral for refinement composition. *}

lemma refinement_compose_neutral_right:
  assumes "sound_REFINEMENT r"
  shows "Concrete r = m \<Longrightarrow> refinement_compose r (refinement_id m) = Some r"
proof(simp add:sound_REFINEMENT_def refinement_compose_def refinement_id_def)
qed

text {* Last, refinement composition is associative. The expression of this
property is not as straightforward as we could expect due to the partialness
of composition. *}
lemma refinement_compose_associative:
  assumes "sound_REFINEMENT r1 \<and> sound_REFINEMENT r2 \<and> sound_REFINEMENT r3"
      and "Concrete r1 = Abstract r2" 
      and "Concrete r2 = Abstract r3"
  shows "\<exists> r12 r23 . Some r12 = refinement_compose r1 r2 \<and> 
         Some r23 = refinement_compose r2 r3 \<and>
         refinement_compose r12 r3 = refinement_compose r1 r23"
proof(simp add:sound_REFINEMENT_def refinement_compose_def, auto)
  from assms(2) show "Concrete r1 = Abstract r2" by simp
next
  from assms(3) show "Concrete r2 = Abstract r3" by simp
qed

