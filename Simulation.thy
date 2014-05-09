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
    \<forall> s1 \<in> states l1 . \<forall> s2 \<in> states l2 . (s1, s2) \<in> r \<longrightarrow>
      (\<forall> t1 \<in> trans l1 . src t1 = s1 \<longrightarrow>
        (\<exists> t2 \<in> trans l2 . (src t2 = s2 \<and> evt t1 = evt t2 \<and> (dst t1, dst t2) \<in> r)))"

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
  "lts_simulation r12 l1 l2 \<and> lts_simulation r23 l2 l3 \<Longrightarrow> lts_simulation (r23 O r12) l1 l3"
  unfolding lts_simulation_def lts_simulation_init_def lts_simulation_transition_def relcomp_def 
sorry

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
unfolding lts_simulates_def
sorry

(*
proof
  from s12 obtain r where "lts_simulation r l2 l1" unfolding lts_simulates_def ..
moreover
  from s23 obtain s where "lts_simulation s l3 l2" unfolding lts_simulates_def ..
ultimately
  obtain x where "x = r O s"
    sorry
  from this show "lts_simulation x l3 l1"
    sorry
qed
*)
  
end
