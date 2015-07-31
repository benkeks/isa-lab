theory AchillesParadox
imports
  Real
begin
--"declare [[show_types]]"

locale AchillesTortoise =
fixes
  a_speed t_speed
  a_start t_start :: real
assumes
  positive_speed: "0 < a_speed" "0 < t_speed" and
  achilles_fast: "a_speed > t_speed" and
  tortoise_ahead: "a_start < t_start"
begin

inductive_set simulation where
  init: "(a_start, t_start) \<in> simulation" |
  step: "(a, t) \<in> simulation 
   \<Longrightarrow>  (let time = (t - a) / a_speed in
     (a + time*a_speed, t + time*t_speed)) 
       \<in> simulation"

lemma no_take_over:
fixes a t
assumes
  "(a, t) \<in> simulation"
shows
  "a < t"
using assms proof (induct "(a, t)" arbitrary: a t)
case init 
  thus "a_start < t_start"
    using tortoise_ahead by simp
next case (step ac tc)
  hence "a = tc" using positive_speed(1) by simp
  moreover have "t = tc + (tc - ac) / a_speed * t_speed" using step(3) by auto
  ultimately show ?case using step(2) positive_speed by auto
qed

end

end
