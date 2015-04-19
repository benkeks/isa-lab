theory Sqrt2
imports
  Complex_Main
  "~~/src/HOL/Number_Theory/Primes"
begin
declare [[show_types]]
notation "sqrt" ("\<surd>")


thm Rats_abs_nat_div_natE

theorem sqrt2_not_rational:
  "\<surd>2 \<notin> \<rat>"
proof 
  assume "\<surd>2 \<in> \<rat>"
  then obtain m n :: nat where
    mn_sqrt_rat: "\<bar>\<surd>2\<bar> = m / n" "n \<noteq> 0" and
    mn_coprimes: "gcd m n = 1"
    using Rats_abs_nat_div_natE[of " \<surd>2"] by blast
  hence "m = \<bar>\<surd>2\<bar> * n" by simp
  hence "m\<^sup>2 = (\<surd>2)\<^sup>2 * n\<^sup>2"
    unfolding power2_eq_square by simp
  also have "... = 2 * n\<^sup>2" by simp
  finally have eq: "m\<^sup>2 = 2 * n\<^sup>2" by (metis real_of_nat_inject)
  hence "2 dvd m\<^sup>2" by simp
  hence m_even: "2 dvd m"
    unfolding power2_eq_square using even_product_nat by simp
  then obtain k where "m = 2 * k" ..  
  with eq have "2 * n\<^sup>2 = 2\<^sup>2 * k\<^sup>2" 
    unfolding power2_eq_square by simp
  hence "n\<^sup>2 = 2 * k\<^sup>2" by simp
  hence "2 dvd n\<^sup>2" ..
  hence n_even: "2 dvd n"
    unfolding power2_eq_square using even_product_nat by simp 
  hence "2 dvd (gcd m n)"
    using m_even gcd_greatest_iff_nat by simp
  thus "False"
    using mn_coprimes by simp
qed

end
