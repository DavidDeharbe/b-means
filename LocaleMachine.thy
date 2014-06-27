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
begin

  definition sound :: "bool" where
    "sound \<equiv> \<forall> s \<in> states . (inv s)"
  
  lemma po:
  assumes po_init: "\<forall> s \<in> init lts. inv s" and
          po_step: "\<forall> t \<in> trans lts. inv (src t) \<longrightarrow> inv (dst t)"
  shows sound
  unfolding sound_def sorry 

end

end
