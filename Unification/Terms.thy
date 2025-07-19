
theory Terms = Main + Swap:

(* terms *)

datatype trm = Abst  string  trm   
             | Susp  "(string \<times> string)list" string
             | Unit                                   
             | Atom  string                           
             | Paar  trm trm                          
             | Func string trm                       

(* swapping operation on terms *)

consts swap  :: "(string \<times> string)list \<Rightarrow> trm \<Rightarrow> trm"
primrec
"swap  pi (Unit)        = Unit"
"swap  pi (Atom a)      = Atom (swapas pi a)"
"swap  pi (Susp pi' X)  = Susp (pi@pi') X"
"swap  pi (Abst a t)    = Abst (swapas pi a) (swap pi t)"
"swap  pi (Paar t1 t2)  = Paar (swap pi t1) (swap pi t2)"
"swap  pi (Func F t)    = Func F (swap pi t)"

lemma [simp]: "swap [] t = t"
apply(induct_tac t)
apply(auto)
done

lemma swap_append[rule_format]: "\<forall>pi1 pi2. swap (pi1@pi2) t = swap pi1 (swap pi2 t)"
apply(induct_tac t, auto)
apply(induct_tac pi1,auto)
apply(induct_tac pi1,auto)
done

lemma swap_empty: "swap pi t=Susp [] X\<longrightarrow> pi=[]"
apply(induct_tac t)
apply(auto)
done

(* depyh of terms *)

consts depth :: "trm \<Rightarrow> nat"
primrec
"depth (Unit)      = 0"
"depth (Atom a)    = 0"
"depth (Susp pi X) = 0"
"depth (Abst a t)  = 1 + depth t"
"depth (Func F t)  = 1 + depth t"
"depth (Paar t t') = 1 + (max (depth t) (depth t'))" 

lemma 
  Suc_max_left:  "Suc(max x y) = z \<longrightarrow> x < z" and
  Suc_max_right: "Suc(max x y) = z \<longrightarrow> y < z"
apply(auto)
apply(simp_all only: max_Suc_Suc[THEN sym] less_max_iff_disj)
apply(simp_all)
done

lemma [simp]: "depth (swap pi t) = depth t" 
apply(induct_tac t,auto)
done

(* occurs predicate and variables in terms *)

consts occurs :: "string \<Rightarrow> trm \<Rightarrow> bool"
primrec 
"occurs X (Unit)       = False"
"occurs X (Atom a)     = False"
"occurs X (Susp pi Y)  = (if X=Y then True else False)"
"occurs X (Abst a t)   = occurs X t"
"occurs X (Paar t1 t2) = (if (occurs X t1) then True else (occurs X t2))"
"occurs X (Func F t)   = occurs X t"

consts vars_trm :: "trm \<Rightarrow> string set"
primrec
"vars_trm (Unit)       = {}"
"vars_trm (Atom a)     = {}"
"vars_trm (Susp pi X)  = {X}"
"vars_trm (Paar t1 t2) = (vars_trm t1)\<union>(vars_trm t2)"
"vars_trm (Abst a t)   = vars_trm t"
"vars_trm (Func F t)   = vars_trm t"


(* subterms and proper subterms *)

consts sub_trms :: "trm \<Rightarrow> trm set"
primrec 
"sub_trms (Unit)       = {Unit}"
"sub_trms (Atom a)     = {Atom a}"
"sub_trms (Susp pi Y)  = {Susp pi Y}"
"sub_trms (Abst a t)   = {Abst a t}\<union>sub_trms t"
"sub_trms (Paar t1 t2) = {Paar t1 t2}\<union>sub_trms t1 \<union>sub_trms t2"
"sub_trms (Func F t)   = {Func F t}\<union>sub_trms t"

consts psub_trms :: "trm \<Rightarrow> trm set"
primrec
"psub_trms (Unit)       = {}"
"psub_trms (Atom a)     = {}"
"psub_trms (Susp pi X)  = {}"
"psub_trms (Paar t1 t2) = sub_trms t1 \<union> sub_trms t2"
"psub_trms (Abst a t)   = sub_trms t"
"psub_trms (Func F t)   = sub_trms t"

lemma psub_sub_trms[rule_format]: 
  "\<forall>t1 . t1 \<in> psub_trms t2 \<longrightarrow>  t1 \<in> sub_trms t2"
apply(induct t2)
apply(auto)
done

lemma t_sub_trms_t: 
  "t\<in> sub_trms t"
apply(induct t)
apply(auto)
done

lemma abst_psub_trms[rule_format]: 
  "\<forall> t1. Abst a t1 \<in> sub_trms t2 \<longrightarrow> t1 \<in> psub_trms t2"
apply(induct_tac t2)
apply(auto)
apply(simp only: t_sub_trms_t)
apply(best dest!: psub_sub_trms)+
done

lemma func_psub_trms[rule_format]: 
  "\<forall> t1. Func F t1 \<in> sub_trms t2 \<longrightarrow> t1 \<in> psub_trms t2"
apply(induct_tac t2)
apply(auto)
apply(best dest!: psub_sub_trms)+
apply(simp add: t_sub_trms_t)
apply(best dest!: psub_sub_trms)
done

lemma paar_psub_trms[rule_format]: 
  "\<forall> t1. Paar t1 t2 \<in> sub_trms t3\<longrightarrow>(t1 \<in> psub_trms t3 \<and> t2 \<in> psub_trms t3)"
apply(induct_tac t3)
apply(auto)
apply(best dest!: psub_sub_trms)+
apply(simp add: t_sub_trms_t)+
apply(best dest!: psub_sub_trms)+
done

end