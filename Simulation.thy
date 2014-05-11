theory Simulation

imports Main LTS

begin
section {* Behaviour: a set of traces *}

text {* We introduce the notion of simulation: a relation between the states of one LTS
and the states of another LTS such that any transition taken by the former can be simulated
by the latter, i.e. the latter can follow a transition that is labeled with the same event,
and leads to a state where it can continue the simulation: *}

definition lts_simulation_init :: "STATE rel \<Rightarrow> LTS \<Rightarrow> LTS \<Rightarrow> bool" where
  "lts_simulation_init r l1 l2 \<equiv> \<forall> s1 \<in> init l1 . \<exists> s2 \<in> init l2 . (s1, s2) \<in> r"

definition lts_simulation_transition :: "STATE rel \<Rightarrow> LTS \<Rightarrow> LTS \<Rightarrow> bool" where
  "lts_simulation_transition r l1 l2 \<equiv> 
    \<forall> s1 s2 . (s1, s2) \<in> r \<longrightarrow>
      (\<forall> t1 \<in> trans l1 . src t1 = s1 \<longrightarrow>
        (\<exists> t2 \<in> trans l2 . src t2 = s2 \<and> evt t1 = evt t2 \<and> (dst t1, dst t2) \<in> r))"

definition lts_simulation :: "STATE rel \<Rightarrow> LTS \<Rightarrow> LTS \<Rightarrow> bool" where
  "lts_simulation r l1 l2 \<equiv> lts_simulation_init r l1 l2 \<and> lts_simulation_transition r l1 l2"

text {* Let us verify some basic properties of simulations. First we have that the
identity relation establishes that a LTS simulates itself. *}
  (* maybe use Id_on (states l) instead of Id ? *)
lemma lts_simulation_identity :
  "lts_simulation Id l l" unfolding lts_simulation_def
proof
  show "lts_simulation_init Id l l" unfolding lts_simulation_init_def Id_def by auto
next
  show "lts_simulation_transition Id l l" unfolding lts_simulation_transition_def Id_def by auto
qed

text {* Second, we have that the composition of two simulation relations 
is a simulation relation. *}
lemma lts_simulation_transitivity:
assumes s12: "lts_simulation r12 l1 l2" and s23: "lts_simulation r23 l2 l3"
shows "lts_simulation (r12 O r23) l1 l3"
proof -
  have "lts_simulation_init (r12 O r23) l1 l3"
  proof -
    from s12 have "lts_simulation_init r12 l1 l2" unfolding lts_simulation_def ..
  moreover
    from s23 have "lts_simulation_init r23 l2 l3" unfolding lts_simulation_def ..
  ultimately
    show "lts_simulation_init (r12 O r23) l1 l3" unfolding lts_simulation_init_def relcomp_def by blast
  qed
moreover
  have "lts_simulation_transition (r12 O r23) l1 l3" unfolding "lts_simulation_transition_def"
  proof
    fix s1
    show "\<forall>s3. (s1, s3) \<in> r12 O r23 \<longrightarrow> (\<forall>t1\<in>LTS.trans l1. src t1 = s1 \<longrightarrow> (\<exists>t2\<in>LTS.trans l3. src t2 = s3 \<and> evt t1 = evt t2 \<and> (dst t1, dst t2) \<in> r12 O r23))"
    proof
      fix s3
      show "(s1, s3) \<in> r12 O r23 \<longrightarrow> (\<forall>t1\<in>LTS.trans l1. src t1 = s1 \<longrightarrow> (\<exists>t2\<in>LTS.trans l3. src t2 = s3 \<and> evt t1 = evt t2 \<and> (dst t1, dst t2) \<in> r12 O r23))"
      proof
        assume 1: "(s1, s3) \<in> r12 O r23"
        show "(\<forall>t1\<in>LTS.trans l1. src t1 = s1 \<longrightarrow> (\<exists>t2\<in>LTS.trans l3. src t2 = s3 \<and> evt t1 = evt t2 \<and> (dst t1, dst t2) \<in> r12 O r23))"
        proof
          fix t1
          assume dom_t1: "t1\<in>LTS.trans l1"
          show "src t1 = s1 \<longrightarrow> (\<exists>t3\<in>LTS.trans l3. src t3 = s3 \<and> evt t1 = evt t3 \<and> (dst t1, dst t3) \<in> r12 O r23)"
          proof
            assume src_t1: "src t1 = s1"
            show "\<exists>t3\<in>LTS.trans l3. src t3 = s3 \<and> evt t1 = evt t3 \<and> (dst t1, dst t3) \<in> r12 O r23"
              proof-
                have "\<exists> t3 . t3 \<in> LTS.trans l3 \<and> src t3 = s3 \<and> evt t1 = evt t3 \<and> (dst t1, dst t3) \<in> r12 O r23"
                proof -
                  from 1 have "\<exists> s2 . (s1, s2) \<in> r12 \<and> (s2, s3) \<in> r23" unfolding relcomp_def by auto
                  then obtain s2 where 2: "(s1, s2) \<in> r12 \<and> (s2, s3) \<in> r23" ..
                moreover
                  from 2 have "(s1, s2) \<in> r12" ..
                  with s12 src_t1 dom_t1 obtain t2 where w12: "t2 \<in> LTS.trans l2 \<and> src t2 = s2 \<and> evt t1 = evt t2 \<and> (dst t1, dst t2) \<in> r12" 
                    unfolding lts_simulation_def lts_simulation_transition_def by blast
                moreover
                  from 2 have "(s2, s3) \<in> r23" by simp
                  with s23 w12 obtain w where "w \<in> LTS.trans l3 \<and> src w = s3 \<and> evt t2 = evt w \<and> (dst t2, dst w) \<in> r23" 
                    unfolding lts_simulation_def lts_simulation_transition_def by blast
                  with w12 have "w \<in> LTS.trans l3 \<and> src w = s3 \<and> evt t1 = evt w \<and> (dst t1, dst w) \<in> r12 O r23" unfolding relcomp_def by auto
                  then show ?thesis ..
                qed
              then show ?thesis by auto
            qed
          qed
        qed
      qed
    qed
  qed
  ultimately show ?thesis unfolding lts_simulation_def ..
qed

text {* Next we carry these properties over to the simulates relation over LTS. *}

text {* Based on the notion of simulation, we introduce the relation simulates on LTS: *}
definition lts_simulates :: "LTS \<Rightarrow> LTS \<Rightarrow> bool" (infixl "\<sim>" 50) where
  "(l1 \<sim> l2) \<equiv> \<exists> r . lts_simulation r l2 l1"

lemma lts_simulates_reflexivity: "l \<sim> l" 
  unfolding lts_simulates_def
proof
  show "lts_simulation Id l l" by (rule lts_simulation_identity)
qed

lemma lts_simulates_transitivity:
assumes
  s12: "l1 \<sim> l2" and s23: "l2 \<sim> l3"
shows
  "l1 \<sim> l3"
proof -
  from s23 obtain s where "lts_simulation s l3 l2" unfolding lts_simulates_def ..
moreover
  from s12 obtain r where "lts_simulation r l2 l1" unfolding lts_simulates_def ..
ultimately
  have "lts_simulation (s O r) l3 l1" 
    by (rule lts_simulation_transitivity[of "s" "l3" "l2" "r" "l1"])
  then have "\<exists> r . lts_simulation r l3 l1" ..
  then show ?thesis unfolding lts_simulates_def by simp
qed
  
end
