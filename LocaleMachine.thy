theory LocaleMachine

imports Main LocaleLTS

begin

locale Machine =
  LTS lts
for
  lts :: "('state, 'event) LTS" 
+
fixes
  inv :: "'state \<Rightarrow> bool"
assumes
  po_init: "\<forall>s \<in> init lts. inv s" and
  po_step: "\<forall>t \<in> trans lts. inv (src t) \<longrightarrow> inv (dst t)"
begin

  lemma inv_states: "\<forall>s\<in>states. inv s"
  using po_init po_step by (rule reachable_induct_predicate)

end (* locale Machine *)

end
