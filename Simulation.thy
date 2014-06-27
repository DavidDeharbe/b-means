theory Simulation

imports Main LTS

begin
section {* Behaviour: a set of traces *}

text {* We introduce the notion of simulation: a relation between the states of one LTS
and the states of another LTS such that any transition taken by the former can be simulated
by the latter, i.e. the latter can follow a transition that is labeled with the same event,
and leads to a state where it can continue the simulation: *}

definition simulation_init :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation_init r l1 l2 \<equiv> \<forall> s1 \<in> init l1 . \<exists> s2 \<in> init l2 . (s1, s2) \<in> r"

definition simulation_step :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation_step r l1 l2 \<equiv> 
    \<forall> s1 s2 . (s1, s2) \<in> r \<longrightarrow>
      (\<forall> t1 \<in> trans l1 . src t1 = s1 \<longrightarrow>
        (\<exists> t2 \<in> trans l2 . src t2 = s2 \<and> lbl t1 = lbl t2 \<and> (dst t1, dst t2) \<in> r))"

definition simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation r l1 l2 \<equiv> simulation_init r l1 l2 \<and> simulation_step r l1 l2"

text {* Let us verify some basic properties of simulations. First we have that the
identity relation establishes that a LTS simulates itself. *}
  (* maybe use Id_on (states l) instead of Id ? *)
lemma simulation_identity : "simulation Id l l" 
  unfolding simulation_def simulation_init_def simulation_step_def by auto

text {* Second, we have that the composition of two simulation relations 
is a simulation relation. *}
lemma simulation_transitivity:
assumes s12: "simulation r12 l1 l2" and s23: "simulation r23 l2 l3"
shows "simulation (r12 O r23) l1 l3"
proof -
  from s12 s23
  have "simulation_init (r12 O r23) l1 l3"
  unfolding simulation_def simulation_init_def relcomp_unfold
  by simp metis
moreover
  from s12 s23
  have "simulation_step (r12 O r23) l1 l3"
  unfolding simulation_step_def simulation_def relcomp_unfold
  by simp metis
  ultimately show ?thesis unfolding simulation_def ..
qed

text {* Next we carry these properties over to the simulates relation over LTS. *}

text {* Based on the notion of simulation, we introduce the relation simulates on LTS: *}
definition simulates :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sim>" 50) where
  "(l1 \<sim> l2) \<equiv> \<exists> r . simulation r l2 l1"

lemma simulates_reflexivity: "l \<sim> l" 
  unfolding simulates_def
proof
  show "simulation Id l l" by (rule simulation_identity)
qed

lemma simulates_transitivity:
assumes
  s12: "l1 \<sim> l2" and s23: "l2 \<sim> l3"
shows
  "l1 \<sim> l3"
proof -
  from s23 obtain s where "simulation s l3 l2" unfolding simulates_def ..
moreover
  from s12 obtain r where "simulation r l2 l1" unfolding simulates_def ..
ultimately
  have "simulation (s O r) l3 l1" 
    by (rule simulation_transitivity[of "s" "l3" "l2" "r" "l1"])
  then show ?thesis unfolding simulates_def by auto
qed
  
end
