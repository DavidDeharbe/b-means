theory Refinement

imports Main Misc Machine Traces

begin

section {* B refinement: two components glued by a relation between states *}

record REFINEMENT =
  Abstract :: MACHINE
  Concrete :: LTS
  Glue :: "STATE rel" (* relates Abstract to Concrete - see wd_REFINEMENT_glue *)
  
definition wd_REFINEMENT_machines :: "REFINEMENT \<Rightarrow> bool" where
  "wd_REFINEMENT_machines r \<equiv> 
    wd_LTS(Lts (Abstract r)) \<and> wd_LTS(Concrete r)"

definition wd_REFINEMENT_glue :: "REFINEMENT \<Rightarrow> bool" where
  "wd_REFINEMENT_glue r \<equiv> Glue r \<subseteq> State(Concrete r) \<times> State(Lts (Abstract r))"

definition sound_REFINEMENT_init :: "REFINEMENT \<Rightarrow> bool" where
  "sound_REFINEMENT_init r \<equiv> \<forall> s \<in> Init (Concrete r) . \<exists> sa \<in> Init(Lts (Abstract r)) . (s, sa) \<in> Glue r"

definition sound_REFINEMENT_trans :: "REFINEMENT \<Rightarrow> bool" where
"sound_REFINEMENT_trans r \<equiv> \<forall> tc \<in> Trans (Concrete r) . \<exists> ta \<in> Trans (Lts (Abstract r)) .
(Src tc, Src ta) \<in> Glue r \<and> (Dst tc, Dst ta) \<in> Glue r \<and> Evt tc = Evt ta" 

definition sound_REFINEMENT :: "REFINEMENT \<Rightarrow> bool" where
"sound_REFINEMENT r \<equiv> sound_REFINEMENT_init r \<and> sound_REFINEMENT_trans r"

text {* A special refinement is one that does not change anything, namely the
identity refinement. It is defined as a function that takes a machine and
returns the identity refinement. *}

definition refinement_id :: "MACHINE \<Rightarrow> REFINEMENT" where
"refinement_id m \<equiv> \<lparr> Abstract = m, Concrete = (Lts m), Glue = Id \<rparr>"

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
  (if Concrete r1 = Lts (Abstract r2) then
    Some \<lparr> Abstract = Abstract r1, Concrete = Concrete r2, Glue = (Glue r2) O (Glue r1)\<rparr>
  else None)"

lemma refinement_compose_soundness:
  assumes 
    "sound_REFINEMENT r1" and "sound_REFINEMENT r2" and
    "refinement_compose r1 r2 = Some r"
  shows "sound_REFINEMENT r"
proof(cases "Concrete r1 = Lts(Abstract r2)")
  case False
    hence "refinement_compose r1 r2 = None" by (simp add:refinement_compose_def)
    with assms(3)
    have "Some r = None" by simp
    thus ?thesis by simp
next
  def rv \<equiv> "\<lparr> Abstract = Abstract r1, Concrete = Concrete r2, Glue = Glue r2 O Glue r1 \<rparr>"
  case True
    then have guard : "Concrete r1 = Lts (Abstract r2)" .
    hence "refinement_compose r1 r2 = Some rv"
      sorry
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
(*        by (simp add: relcomp_totality) *)
      moreover
        with guard have "Init(Concrete r1) = Init(Lts(Abstract r2))" by simp
      ultimately
      show "\<forall>s\<in>Init (Concrete r2). \<exists>sa\<in>Init(Lts (Abstract r2)). (s, sa) \<in> Glue r2 \<Longrightarrow>
            \<forall>s\<in>Init (Concrete r1). \<exists>sa\<in>Init(Lts (Abstract r1)). (s, sa) \<in> Glue r1 \<Longrightarrow> 
            \<forall>s\<in>Init (Concrete r2). \<exists>sa\<in>Init(Lts (Abstract r1)). (s, sa) \<in> Glue r2 O Glue r1" by simp
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

lemma refinement_paths:
assumes "sound_REFINEMENT r"
shows "\<forall> pc \<in> paths(Concrete r) . \<exists> pa \<in> paths(Abstract r) .
  (fst pc, fst pa) \<in> (Glue r)"
sorry


lemma
  assumes
    "sound_REFINEMENT r"
  shows
    "traces (Concrete r) \<subseteq> traces (Abstract r)"
  proof(simp only:traces_def)
    have "p \<in> {path_events p |p. p \<in> paths (Concrete r)} \<Longrightarrow> p \<in> {path_events p |p. p \<in> paths (Abstract r)}"
    sorry
    then show "{path_events p |p. p \<in> paths (Concrete r)} \<subseteq> {path_events p |p. p \<in> paths (Abstract r)}"
      sorry
  qed

end
