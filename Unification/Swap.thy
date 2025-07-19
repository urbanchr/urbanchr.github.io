
theory Swap = Main:

consts 
  swapa   :: "(string \<times> string) \<Rightarrow> string \<Rightarrow> string"
  swapas  :: "(string \<times> string)list \<Rightarrow> string \<Rightarrow> string"
primrec
  "swapa (b,c) a = (if b = a then c else (if c = a then b else a))"

primrec
  "swapas []     a = a"
  "swapas (x#pi) a = swapa x (swapas pi a)"

lemma [simp]: 
  "swapas [(a,a)] b=b"
apply(auto)
done

lemma swapas_append: 
  "swapas (pi1@pi2) a = swapas pi1 (swapas pi2 a)"
apply(induct_tac pi1, auto)
done 

lemma [simp]: 
  "swapas (rev pi) (swapas pi a) = a"
apply(induct_tac pi)
apply(simp_all add: swapas_append, auto)
done

lemma swapas_rev_pi_a: 
  "swapas pi a = b \<Longrightarrow> swapas (rev pi) b = a"
apply(auto)
done

lemma [simp]: 
  "swapas pi (swapas (rev pi) a) = a"
apply(rule swapas_rev_pi_a[of "(rev pi)" _ _,simplified])
apply(simp)
done

lemma swapas_rev_pi_b: 
  "swapas (rev pi) a = b \<Longrightarrow> swapas pi b = a"
apply(auto)
done

lemma swapas_comm: 
  "(swapas (pi@[(a,b)]) c) = (swapas ([(swapas pi a,swapas pi b)]@pi) c)"
apply(auto)
apply(simp_all only: swapas_append)
apply(auto)
apply(drule swapas_rev_pi_a, simp)
apply(drule swapas_rev_pi_a, simp)
done

end