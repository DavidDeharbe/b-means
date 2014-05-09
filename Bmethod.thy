theory Bmethod

imports Main LTS Simulation

begin

section {* B machine *}

text {* A B machine is a state-transition system together with an invariant. An invariant
is a predicate on the states of the system. *}

record B_machine =
  lts :: LTS
  invariant :: "STATE \<Rightarrow> bool"
  
text {* A B machine is considered correct when all the reachable states satisfy the
        invariant. *}

definition sound_B_machine :: "B_machine \<Rightarrow> bool" where
  "sound_B_machine m \<equiv> \<forall> s \<in> states (lts m) . (invariant m) s"

text {* The following theorem states two sufficient conditions to establish that a machine is
correct. *}

theorem machine_po:
  assumes po_init: "\<forall> s \<in> init (lts m) . (invariant m) s" and 
          po_step: "\<forall> t \<in> trans (lts m) . (invariant m)(src t) \<longrightarrow> (invariant m)(dst t)"
  shows "sound_B_machine m"
proof-
  from assms have "\<forall> s \<in> states (lts m). (invariant m) s"
    proof(rule reachable_induct_predicate[of "(lts m)" "(invariant m)"])
    qed
  then show ?thesis by (simp only:sound_B_machine_def)
qed

section {* B refinement: two components glued by a relation between states *}

record B_refinement =
  abstract :: LTS
  concrete :: LTS
  invariant :: "STATE \<times> STATE \<Rightarrow> bool" (* relates Abstract to Concrete - see wd_B_refinement_glue *)
  
definition sound_B_refinement :: "B_refinement \<Rightarrow> bool" where
"sound_B_refinement r \<equiv> lts_simulation {(s, s') | s s' . (invariant r) (s, s') } (concrete r) (abstract r)"

text {* A special refinement is one that does not change anything, namely the
identity refinement. It is defined as a function that takes a machine and
returns the identity refinement. *}

definition refinement_id :: "LTS \<Rightarrow> B_refinement" where
"refinement_id m \<equiv> \<lparr> abstract = m, concrete = m, invariant = (\<lambda> p . fst p = snd p) \<rparr>"

text {* We have that the identity refinement is sound. *}

lemma "sound_B_refinement(refinement_id m)"
sorry

text {* Next, we definement composition of refinements. This is only defined if the
composed refinements have matching set of states, otherwise it is left
undefined. *}

definition refinement_compose :: "B_refinement \<Rightarrow> B_refinement \<Rightarrow> B_refinement option" where
"refinement_compose r1 r2 \<equiv> 
  (if concrete r1 = abstract r2 then
  Some \<lparr> abstract = abstract r1, concrete = concrete r2, invariant = \<lambda> p . \<exists> s . (invariant r1)(fst p, s) \<and> (invariant r2)(s, snd p)\<rparr>
  else None)"

lemma refinement_compose_soundness:
  assumes 
    "sound_B_refinement r1" and "sound_B_refinement r2" and
    "refinement_compose r1 r2 = Some r"
  shows "sound_B_refinement r"
proof(cases "concrete r1 = abstract r2")
  case False
    hence "refinement_compose r1 r2 = None" by (simp add:refinement_compose_def)
    with assms(3)
    have "Some r = None" by simp
    thus ?thesis by simp
next
  case True
  assume "concrete r1 = abstract r2"
  show "sound_B_refinement r" unfolding sound_B_refinement_def lts_simulation_def lts_simulation_init_def lts_simulation_transition_def
  sorry
qed
(*
  let ?inv = "\<lambda> p . \<exists> s . (invariant r1)(fst p, s) \<and> (invariant r2)(s, snd p)"
  def rv \<equiv> "\<lparr> abstract = abstract r1, concrete = concrete r2, invariant = ?inv \<rparr>"
    hence "refinement_compose r1 r2 = Some rv"
      sorry
    with assms(3)
      have r: "r = rv" by simp
    from assms(2)
      have i2: "sound_B_refinement_init r2" by (simp add: sound_B_refinement_def)
    from assms(1)
      have i1: "sound_B_refinement_init r1" by (simp add: sound_B_refinement_def)    
    from i2 and i1
      have i: "sound_B_refinement_init rv" unfolding sound_B_refinement_init_def rv_def
    proof -
      have "\<forall>s\<in>init (concrete r2). \<exists>sa\<in>init (abstract r2). (invariant r2) (s, sa) \<Longrightarrow>
            \<forall>s\<in>init (abstract r2). \<exists>sa\<in>init (abstract r1). (invariant r1) (s, sa) \<Longrightarrow> 
            \<forall>s\<in>init (concrete r2). \<exists>sa\<in>init (abstract r1). ?inv(s, sa)"
            sorry
(*        by (simp add: relcomp_totality) *)
      moreover
        have "init(concrete r1) = init(abstract r2)"
          sorry
      ultimately
      show "\<forall>s\<in>init (concrete r2). \<exists>sa\<in>init(abstract r2). (invariant r2)(s, sa) \<Longrightarrow>
            \<forall>s\<in>init (concrete r1). \<exists>sa\<in>init(abstract r1). (invariant r1)(s, sa) \<Longrightarrow> 
            \<forall>s\<in>init (concrete r2). \<exists>sa\<in>init(abstract r1). ?inv(s, sa)"
      sorry
    qed
  moreover  
    from assms(1)
      have t1: "sound_B_refinement_trans r1" by (simp add: sound_B_refinement_def)
    from assms(2)
      have t2: "sound_B_refinement_trans r2" by (simp add: sound_B_refinement_def)
    from t1 and t2
      have t: "sound_B_refinement_trans rv"
      proof (simp add:sound_B_refinement_trans_def rv_def)
        have 
          "\<forall>tc\<in>Trans (Concrete r1). \<exists>ta\<in>Trans (Abstract r1). (Src tc, Src ta) \<in> Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r1 \<and> Evt tc = Evt ta \<Longrightarrow>
           \<forall>tc\<in>Trans (Concrete r2). \<exists>ta\<in>Trans (Concrete r1). (Src tc, Src ta) \<in> Glue r2 \<and> (Dst tc, Dst ta) \<in> Glue r2  \<and> Evt tc = Evt ta \<Longrightarrow>
           \<forall>tc\<in>Trans(Concrete r2). \<exists>ta\<in>Trans(Abstract r1). (Src tc, Src ta) \<in> Glue r2 O Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r2 O Glue r1 \<and> Evt tc = Evt ta"
          by (simp add: relcomp_pair)
        moreover
          with guard have "Trans(Concrete r1) = Trans(Lts(Abstract r2))" by simp
        ultimately
        show
          "\<forall>tc\<in>Trans (Concrete r1). \<exists>ta\<in>Trans (Abstract r1). (Src tc, Src ta) \<in> Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r1 \<and> Evt tc = Evt ta \<Longrightarrow>
           \<forall>tc\<in>Trans (Concrete r2). \<exists>ta\<in>Trans (Abstract r2). (Src tc, Src ta) \<in> Glue r2 \<and> (Dst tc, Dst ta) \<in> Glue r2 \<and> Evt tc = Evt ta \<Longrightarrow>
           \<forall>tc\<in>Trans(Concrete r2). \<exists>ta\<in>Trans(Abstract r1). (Src tc, Src ta) \<in> Glue r2 O Glue r1 \<and> (Dst tc, Dst ta) \<in> Glue r2 O Glue r1 \<and> Evt tc = Evt ta"
          by simp
      qed
  ultimately
    have "sound_B_refinement rv" 
      by (simp add:sound_B_refinement_def)
    with r show "sound_B_refinement r" by simp
qed
 *)
text {* We now want to verify that our definition of refinement composition satisfies
some simple properties. First any identity refinement is left-neutral: *}

lemma refinement_compose_neutral_left:
  assumes "sound_B_refinement r"
  shows "abstract r = m \<Longrightarrow> refinement_compose (refinement_id m) r = Some r"
proof(simp add:sound_B_refinement_def refinement_compose_def refinement_id_def)
qed

text {* Second, any identity refinement is right-neutral for refinement composition. *}

lemma refinement_compose_neutral_right:
  assumes "sound_B_refinement r"
  shows "concrete r = m \<Longrightarrow> refinement_compose r (refinement_id m) = Some r"
proof(simp add:sound_B_refinement_def refinement_compose_def refinement_id_def)
qed

text {* Last, refinement composition is associative. The expression of this
property is not as straightforward as we could expect due to the partialness
of composition. *}
lemma refinement_compose_associative:
  assumes "sound_B_refinement r1 \<and> sound_B_refinement r2 \<and> sound_B_refinement r3"
      and "concrete r1 = abstract r2" 
      and "concrete r2 = abstract r3"
  shows "\<exists> r12 r23 . Some r12 = refinement_compose r1 r2 \<and> 
         Some r23 = refinement_compose r2 r3 \<and>
         refinement_compose r12 r3 = refinement_compose r1 r23"
proof(simp add:sound_B_refinement_def refinement_compose_def, auto)
  from assms(2) show "concrete r1 = abstract r2" by simp
next
  from assms(3) show "concrete r2 = abstract r3" by simp
qed

(*
lemma refinement_paths:
assumes "sound_B_refinement r"
shows "\<forall> pc \<in> lts_traces(concrete r) . \<exists> pa \<in> lts_traces(abstract r) . (invariant r) (fst pc, fst pa)"
sorry
*)

lemma assumes "sound_B_refinement r" shows "lts_traces (concrete r) \<subseteq> lts_traces (abstract r)"
  sorry

section {* B development *}

type_synonym B_design = "B_refinement list"

inductive sound_B_design :: "B_design \<Rightarrow> bool" where
  base: "sound_B_design []" |
  step: "\<lbrakk> sound_B_refinement x; xs \<noteq> [] \<longrightarrow> concrete x = abstract (hd xs) \<and> sound_B_design xs \<rbrakk> \<Longrightarrow> sound_B_design (x # xs)"
   
record B_development =
  spec :: B_machine
  design :: B_design

definition sound_B_development :: "B_development \<Rightarrow> bool" where
  "sound_B_development dev \<equiv> 
    sound_B_machine (spec dev) \<and> sound_B_design (design dev) \<and>
    (design dev \<noteq> [] \<longrightarrow> (B_machine.lts (spec dev)) = (abstract (hd (design dev))))"
    
end
