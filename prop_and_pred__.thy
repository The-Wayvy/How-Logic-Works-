theory Scratch
  imports Main
begin 

notepad
begin
  have "P \<and> Q \<Longrightarrow> P"
    by (rule conjunct1)
end
 
  theorem left_conj: "P \<and> Q \<Longrightarrow> P"
    by (rule conjunct1)

  theorem two_nested_left: "(P\<and>Q)\<and>R \<Longrightarrow> P"
  proof -
      assume h_1: "(P\<and>Q)\<and>R"  
      have h_2: "P\<and>Q" using h_1 by (rule left_conj)
      show "P" using h_2 by (rule left_conj)
    qed

  theorem right_conj: "P \<and> Q \<Longrightarrow> Q"
    by (rule conjunct2)

  theorem and_intro: "\<lbrakk>P;Q\<rbrakk> \<Longrightarrow> P \<and> Q"
    by (rule conjI)

notepad 

begin

  have "\<lbrakk>P;Q\<rbrakk> \<Longrightarrow> P\<and>Q "
  proof - 
    assume "P"
    assume "Q"
    show "P\<and>Q" by (rule conjI [OF \<open>P\<close> \<open>Q\<close>])
  qed

have "P \<and> Q \<Longrightarrow> P"
proof -
  assume "P \<and> Q"
 (* from \<open>P \<and> Q\<close> show "P" by (rule conjunct1)*)
  show "P" using \<open>P \<and> Q\<close> by (rule conjunct1)
qed

have "P \<and> Q \<Longrightarrow> Q"
proof -
  assume "P \<and> Q"
 (* from \<open>P \<and> Q\<close> show "P" by (rule conjunct1)*)
  show "Q" using \<open>P \<and> Q\<close> by (rule conjunct2)
qed

have "P \<and> Q \<Longrightarrow> P"
proof -
  assume "P \<and> Q"
  have "P" by (rule conjunct1[OF \<open>P \<and> Q\<close>]) 
  show "P" by fact (*using \<open>P\<close> by assumption*)
qed

  have "(P\<and>Q)\<and>(R\<and>P) \<Longrightarrow> P"
  proof - 
    assume "(P\<and>Q)\<and>(R\<and>P)" 
    have "P\<and>Q" by 
        (rule conjunct1[OF \<open>(P\<and>Q)\<and>(R\<and>P)\<close>])
    show "P" using \<open>P \<and> Q\<close> by (rule conjunct1)
  qed

  have "P \<Longrightarrow> P\<and>P "
  proof - 
    assume "P"
    show "P\<and>P" by (rule conjI [OF \<open>P\<close> \<open>P\<close>])
  qed

(*2.05*)
  have "\<lbrakk>P\<and>Q;R\<rbrakk>\<Longrightarrow>(P\<and>Q)\<and>R"
  proof -
    assume "P\<and>Q"
    assume "R"
    show "(P\<and>Q)\<and>R" by (rule conjI[OF \<open>P\<and>Q\<close> \<open>R\<close>]) 
  qed

end
(*2.1.1 *)
theorem and_comm: "P\<and>Q \<Longrightarrow> Q\<and>P"
  proof -
    assume "P\<and>Q"
    have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
    show "Q\<and>P" by (rule conjI[OF \<open>Q\<close> \<open>P\<close>])
  qed

notepad
begin

(*2.1.2*)
  have "(P\<and>Q)\<and>R \<Longrightarrow> P\<and>(Q\<and>R)"
  proof -
    assume "(P\<and>Q)\<and>R"
    have "P\<and>Q" using \<open>(P\<and>Q)\<and>R\<close> by (rule conjunct1)
    have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2) 
    have "R" using \<open>(P\<and>Q)\<and>R\<close> by (rule conjunct2)
    have "Q\<and>R" by (rule conjI[OF \<open>Q\<close> \<open>R\<close>])
    show "P\<and>(Q\<and>R)" by (rule conjI[OF \<open>P\<close> \<open>Q\<and>R\<close>])
  qed

(*2.1.3*)
  have "P\<and>Q \<Longrightarrow> (P\<or>R)\<and>(R\<or>Q)"
  proof -
    assume "P\<and>Q"
    have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
    have "P\<or>R" using \<open>P\<close> by (rule disjI1)
    have "R\<or>Q" using \<open>Q\<close> by (rule disjI2)
    show "(P\<or>R)\<and>(R\<or>Q)" using \<open>P\<or>R\<close> \<open>R\<or>Q\<close> by (rule conjI)
  qed

(*2.1.4*)
  have "P \<Longrightarrow> P\<or>P"
  proof -
    assume "P"
    show "P\<or>P" using \<open>P\<close> by (rule disjI2) 
  qed

(*2.2.1*)
  have "P\<and>Q \<Longrightarrow> Q\<or>R"
  proof -
    assume "P\<and>Q"
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
    show "Q\<or>R" using \<open>Q\<close> by (rule disjI1)
  qed

(*2.2.2*)
  have "P\<and>Q  \<Longrightarrow> (P\<or>R)\<and>(Q\<or>R)"
  proof -
    assume "P\<and>Q"
    have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
    have "P\<or>R" using \<open>P\<close> by (rule disjI1)
    have "Q\<or>R" using \<open>Q\<close> by (rule disjI1)
    show "(P\<or>R)\<and>(Q\<or>R)" using \<open>P\<or>R\<close>  \<open>Q\<or>R\<close> by (rule conjI)
  qed

(*2.2.3*)
  have "P \<Longrightarrow> Q\<or>(P\<or>Q)"
  proof -
    assume "P"
    have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
    show "Q\<or>(P\<or>Q)" using \<open>P\<or>Q\<close> by (rule disjI2) 
  qed


(*2.2.4*)
  have "P \<Longrightarrow> (P\<or>R)\<and>(P\<or>Q)"
  proof -
    assume "P"
    have "P\<or>R" using \<open>P\<close> by (rule disjI1)
    have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
    show "(P\<or>R)\<and>(P\<or>Q)" using \<open>P\<or>R\<close>  \<open>P\<or>Q\<close> by (rule conjI) 
  qed

(*2.2.5*)
  have "\<lbrakk>(P\<or>Q)\<longrightarrow>R ; P\<rbrakk> \<Longrightarrow> R"
  proof -
    assume "(P\<or>Q)\<longrightarrow>R"
    assume "P"
    have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
    show "R" using \<open>(P\<or>Q)\<longrightarrow>R\<close> \<open>P\<or>Q\<close> by (rule mp)
  qed

(*2.2.6*)
  have "\<lbrakk>P\<longrightarrow>(Q\<longrightarrow>R) ; P\<and>Q\<rbrakk> \<Longrightarrow> R"
  proof -
    assume "P\<longrightarrow>(Q\<longrightarrow>R)"
    assume "P\<and>Q"
    have "P" and "Q" using \<open>P\<and>Q\<close> by (rule conjunct1, rule conjunct2)
    have "Q\<longrightarrow>R" using \<open>P\<longrightarrow>(Q\<longrightarrow>R)\<close> \<open>P\<close> by (rule mp)
    show R using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)  
    (*have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)*)
  qed

(*2.3.1*)
  have "\<lbrakk>P ; P\<longrightarrow>Q ; P\<longrightarrow>(Q\<longrightarrow>R)\<rbrakk> \<Longrightarrow> R"
  proof - 
    assume "P"
    assume "P\<longrightarrow>Q"
    assume "P\<longrightarrow>(Q\<longrightarrow>R)"
    have "Q "using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
    have "Q\<longrightarrow>R" using \<open>P\<longrightarrow>(Q\<longrightarrow>R)\<close> \<open>P\<close> by (rule mp)
    show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
  qed

(*2.3.2*)
  have "\<lbrakk>(A\<or>B)\<longrightarrow>T ; Z\<longrightarrow>A ; T\<longrightarrow>W ; Z\<rbrakk> \<Longrightarrow> W"
  proof -
    assume "(A\<or>B)\<longrightarrow>T"
    assume "Z\<longrightarrow>A"
    assume "T\<longrightarrow>W"
    assume "Z"
    have "A" using \<open>Z\<longrightarrow>A\<close> \<open>Z\<close> by (rule mp)
    have "A\<or>B" using \<open>A\<close> by (rule disjI1)
    have "T" using \<open>(A\<or>B)\<longrightarrow>T\<close> \<open>A\<or>B\<close> by (rule mp)
    show "W" using \<open>T\<longrightarrow>W\<close> \<open>T\<close> by (rule mp)  
  qed

(*2.3.3*)
  have "\<lbrakk>(A\<longrightarrow>B)\<and>(C\<longrightarrow>A) ; (C\<and>(W\<longrightarrow>Z))\<and>W\<rbrakk> \<Longrightarrow> (B\<or>D)\<and>(Z\<or>E)"
  proof -
    assume "(A\<longrightarrow>B)\<and>(C\<longrightarrow>A)"
    assume "(C\<and>(W\<longrightarrow>Z))\<and>W"
    have "A\<longrightarrow>B" using \<open>(A\<longrightarrow>B)\<and>(C\<longrightarrow>A)\<close> by (rule conjunct1) 
    have "C\<longrightarrow>A" using \<open>(A\<longrightarrow>B)\<and>(C\<longrightarrow>A)\<close> by (rule conjunct2)
    have "W" using \<open>(C\<and>(W\<longrightarrow>Z))\<and>W\<close> by (rule conjunct2)
    have "C\<and>(W\<longrightarrow>Z)" using \<open>(C\<and>(W\<longrightarrow>Z))\<and>W\<close> by (rule conjunct1)  
    have "C" using \<open>C\<and>(W\<longrightarrow>Z)\<close> by (rule conjunct1)
    have "W\<longrightarrow>Z" using \<open>C\<and>(W\<longrightarrow>Z)\<close> by (rule conjunct2)  
    have "Z" using \<open>W\<longrightarrow>Z\<close> \<open>W\<close> by (rule mp)
    have "Z\<or>E" using \<open>Z\<close> by (rule disjI1)
    have "A" using \<open>C\<longrightarrow>A\<close> \<open>C\<close> by (rule mp)
    have "B" using \<open>A\<longrightarrow>B\<close> \<open>A\<close> by (rule mp)
    have "B\<or>D" using \<open>B\<close> by (rule disjI1)
    show "(B\<or>D)\<and>(Z\<or>E)" using \<open>B\<or>D\<close> \<open>Z\<or>E\<close> by (rule conjI)
  qed

(*2.3.4*)
  have "\<lbrakk>P ; P\<longrightarrow>(P\<longrightarrow>Q)\<rbrakk> \<Longrightarrow> Q"
  proof -
    assume "P"
    assume "P\<longrightarrow>(P\<longrightarrow>Q)"
    have "P\<longrightarrow>Q" using \<open>P\<longrightarrow>(P\<longrightarrow>Q)\<close> \<open>P\<close> by (rule mp)
    show "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
  qed

(*2.3.5*)
  have "P\<and>(P\<longrightarrow>Q) \<Longrightarrow> P\<and>Q"
  proof -
    assume "P\<and>(P\<longrightarrow>Q)"
    have "P" using \<open>P\<and>(P\<longrightarrow>Q)\<close> by (rule conjunct1)
    have "P\<longrightarrow>Q" using \<open>P\<and>(P\<longrightarrow>Q)\<close> by (rule conjunct2)
    have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
    show "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
  qed
end 

(*2.4.0*)
theorem mt: "\<lbrakk>P\<longrightarrow>Q ; \<not>Q\<rbrakk> \<Longrightarrow> \<not>P"
  proof -
    assume "P\<longrightarrow>Q"
    assume "\<not>Q"
    have "P \<Longrightarrow> False"
    proof -
      assume "P"
      have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
      show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
    qed
    show "\<not>P" using \<open>P \<Longrightarrow> False\<close> by (rule notI)
  qed 

theorem notnotI: "P \<Longrightarrow> \<not>\<not>P"
proof - 
  assume "P"
  have "\<not>P \<Longrightarrow> False"
  proof -
    assume "\<not>P"
    show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
  qed
  show "\<not>\<not>P" using \<open>\<not>P \<Longrightarrow> False\<close> by (rule notI) 
qed
  

notepad
begin
(*2.4.1.1*)
  have "\<lbrakk>Q\<longrightarrow>(P\<longrightarrow>R) ; \<not>R\<and>Q \<rbrakk> \<Longrightarrow> \<not>P"
  proof -
    assume "Q\<longrightarrow>(P\<longrightarrow>R)"
    assume "\<not>R\<and>Q"
    have "\<not>R" using \<open>\<not>R\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>\<not>R\<and>Q\<close> by (rule conjunct2)
    have "P\<longrightarrow>R" using \<open>Q\<longrightarrow>(P\<longrightarrow>R)\<close> \<open>Q\<close> by (rule mp)
    have "P \<Longrightarrow> False"
      proof -
        assume "P"
        have "R" using \<open>P\<longrightarrow>R\<close> \<open>P\<close> by (rule mp)
        show False using \<open>\<not>R\<close> \<open>R\<close> by (rule notE)
      qed
    show "\<not>P" using \<open>P \<Longrightarrow> False\<close> by (rule notI) 
  qed

(*2.4.1.2*)
  have "\<lbrakk>Q\<longrightarrow>(P\<longrightarrow>R) ; \<not>R\<and>Q \<rbrakk> \<Longrightarrow> \<not>P"
  proof -
    assume "Q\<longrightarrow>(P\<longrightarrow>R)"
    assume "\<not>R\<and>Q"
    have "\<not>R" using \<open>\<not>R\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>\<not>R\<and>Q\<close> by (rule conjunct2)
    have "P\<longrightarrow>R" using \<open>Q\<longrightarrow>(P\<longrightarrow>R)\<close> \<open>Q\<close> by (rule mp)
    show "\<not>P" using \<open>P\<longrightarrow>R\<close> \<open>\<not>R\<close> by (rule mt)
  qed

(*2.4.2*)
  have "\<not>\<not>\<not>P \<Longrightarrow> \<not>P"
  proof -
    assume "\<not>\<not>\<not>P"
    show "\<not>P" using \<open>\<not>\<not>\<not>P\<close> by (rule notnotD)
  qed


have "P \<longrightarrow> P"
proof (rule impI)
  assume "P"
  show "P" using \<open>P\<close> by assumption
qed

have "P \<longrightarrow> (P\<or>Q)"
proof (rule impI)
  assume "P"
  show "P\<or>Q" using \<open>P\<close> by (rule disjI1)
qed


(*2.4.3*)
  have "P\<longrightarrow>\<not>Q \<Longrightarrow> Q\<longrightarrow>\<not>P"
  proof -
    assume "P\<longrightarrow>\<not>Q"
    show "Q\<longrightarrow>\<not>P"
    proof (rule impI)
      assume "Q"
      have "\<not>\<not>Q" using \<open>Q\<close> by (rule notnotI)
      show "\<not>P" using \<open>P\<longrightarrow>\<not>Q\<close> \<open>\<not>\<not>Q\<close> by (rule mt)
    qed 
  qed 
    
(*2.4.4*)
  have "\<lbrakk>\<not>(P\<longrightarrow>Q)\<longrightarrow>Q ; \<not>Q\<rbrakk> \<Longrightarrow> \<not>P"
  proof -
    assume "\<not>(P\<longrightarrow>Q)\<longrightarrow>Q"
    assume "\<not>Q"
    have "\<not>\<not>(P\<longrightarrow>Q)" using \<open>\<not>(P\<longrightarrow>Q)\<longrightarrow>Q\<close> \<open>\<not>Q\<close> by (rule mt)
    have "P\<longrightarrow>Q" using \<open>\<not>\<not>(P\<longrightarrow>Q)\<close> by (rule notnotD)
    show "\<not>P" using \<open>P\<longrightarrow>Q\<close> \<open>\<not>Q\<close> by (rule mt)
  qed

(*2.5.1.1*)
  have "P\<and>(Q\<and>R) \<Longrightarrow> (P\<and>Q)\<and>R"
  proof -
    assume "P\<and>(Q\<and>R)"
    have "P" using \<open>P\<and>(Q\<and>R)\<close> by (rule conjunct1)
    have "Q\<and>R" using \<open>P\<and>(Q\<and>R)\<close> by (rule conjunct2)
    have "Q" using \<open>Q\<and>R\<close> by (rule conjunct1)
    have "R" using \<open>Q\<and>R\<close> by (rule conjunct2)
    have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
    show "(P\<and>Q)\<and>R" using \<open>P\<and>Q\<close> \<open>R\<close> by (rule conjI)
  qed

(*2.5.1.2*)
  have "(P\<and>Q)\<and>R \<Longrightarrow> P\<and>(Q\<and>R)"
  proof -
    assume "(P\<and>Q)\<and>R"
    have "P\<and>Q" using \<open>(P\<and>Q)\<and>R\<close> by (rule conjunct1)
    have "R" using \<open>(P\<and>Q)\<and>R\<close> by (rule conjunct2)
    have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
    have "Q\<and>R" using \<open>Q\<close> \<open>R\<close> by (rule conjI)
    show "P\<and>(Q\<and>R)" using \<open>P\<close> \<open>Q\<and>R\<close> by (rule conjI)
  qed

(*2.5.2.1*)
  have "P \<Longrightarrow> P\<and>P"
  proof -
    assume "P"
    show "P\<and>P" using \<open>P\<close> \<open>P\<close> by (rule conjI)
  qed

(*2.5.2.2*)
  have "P\<and>P \<Longrightarrow> P"
  proof -
    assume "P\<and>P"
    show "P" using \<open>P\<and>P\<close> by (rule conjunct1)
  qed

(*2.7.1*)
  have "\<lbrakk>\<not>P ; \<not>\<not>Q\<longrightarrow>P\<rbrakk> \<Longrightarrow> \<not>Q"
  proof -
    assume "\<not>P"
    assume "\<not>\<not>Q\<longrightarrow>P"
    have "\<not>\<not>\<not>Q" using \<open>\<not>\<not>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
    show "\<not>Q" using \<open>\<not>\<not>\<not>Q\<close> by (rule notnotD)
  qed

(*2.7.2*)
  have "\<lbrakk>P ; P\<longrightarrow>(P\<longrightarrow>Q)\<rbrakk> \<Longrightarrow> Q"
  proof -
    assume "P"
    assume "P\<longrightarrow>(P\<longrightarrow>Q)"
    have "P\<longrightarrow>Q" using \<open>P\<longrightarrow>(P\<longrightarrow>Q)\<close> \<open>P\<close> by (rule mp)
    show "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
  qed

(*2.7.3*)
  have "\<lbrakk>P ; (P\<and>P)\<longrightarrow>Q\<rbrakk> \<Longrightarrow> Q"
  proof -
    assume "P"
    assume "(P\<and>P)\<longrightarrow>Q"
    have "P\<and>P" using \<open>P\<close> \<open>P\<close> by (rule conjI)
    show "Q" using \<open>(P\<and>P)\<longrightarrow>Q\<close> \<open>P\<and>P\<close> by (rule mp)
  qed

(*2.7.4*)
    have "P \<Longrightarrow> Q\<or>(\<not>\<not>P\<or>R)"
    proof -
      assume "P"
      have "\<not>\<not>P" using \<open>P\<close> by (rule notnotI)
      have "\<not>\<not>P\<or>R" using \<open>\<not>\<not>P\<close> by (rule disjI1)
      show "Q\<or>(\<not>\<not>P\<or>R)" using \<open>\<not>\<not>P\<or>R\<close> by (rule disjI2)
    qed

(*3.0.1*)
    have "P \<Longrightarrow> P\<or>Q"
    proof -
      assume "P"
      show "P\<or>Q" using \<open>P\<close> by (rule disjI1)
    qed

(*3.0.2*)
    have "\<lbrakk>P; (P\<or>Q)\<longrightarrow>R\<rbrakk> \<Longrightarrow> R"
    proof -
      assume "P"
      assume "(P\<or>Q)\<longrightarrow>R"
      have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
      show "R" using \<open>(P\<or>Q)\<longrightarrow>R\<close> \<open>P\<or>Q\<close> by (rule mp)
    qed

(*3.0.3*)
    have "\<lbrakk>P ; Q\<rbrakk> \<Longrightarrow> (P\<and>Q)\<and>P"
    proof -
      assume "P"
      assume "Q"
      have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
      show "(P\<and>Q)\<and>P" using \<open>P\<and>Q\<close> \<open>P\<close> by (rule conjI)
    qed

(*3.0.4*)
    have "P\<and>\<not>\<not>Q \<Longrightarrow> Q\<or>R"
    proof -
      assume "P\<and>\<not>\<not>Q"
      have "\<not>\<not>Q" using \<open>P\<and>\<not>\<not>Q\<close> by (rule conjunct2)
      have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
      show "Q\<or>R" using \<open>Q\<close> by (rule disjI1)
    qed

end 
(*3.0.5*)
theorem contrapose: "P\<longrightarrow>Q \<Longrightarrow> \<not>Q\<longrightarrow>\<not>P"
    proof -
      assume "P\<longrightarrow>Q"
      show "\<not>Q\<longrightarrow>\<not>P"
      proof (rule impI)
        assume "\<not>Q"
        show "\<not>P" using \<open>P\<longrightarrow>Q\<close> \<open>\<not>Q\<close> by (rule mt)
        qed 
      qed

notepad 
begin

(*3.0.6*)
      have "\<lbrakk>P\<longrightarrow>Q ; Q\<longrightarrow>R\<rbrakk> \<Longrightarrow> P\<longrightarrow>R"
      proof -
        assume "P\<longrightarrow>Q"
        assume "Q\<longrightarrow>R"
        show "P\<longrightarrow>R"
        proof (rule impI)
          assume "P"
          have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
          show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
        qed
      qed

(*3.0.7*)
      have "(P\<and>Q)\<longrightarrow>R \<Longrightarrow> P\<longrightarrow>(Q\<longrightarrow>R)"
      proof -
        assume "(P\<and>Q)\<longrightarrow>R"
        show "P\<longrightarrow>(Q\<longrightarrow>R)"
        proof (rule impI)
          assume "P"
          show "Q\<longrightarrow>R"
          proof (rule impI)
            assume "Q"
            have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
            show "R" using \<open>(P\<and>Q)\<longrightarrow>R\<close> \<open>P\<and>Q\<close> by (rule mp)
          qed
        qed
      qed

(*3.0.8*)
      have "Q\<longrightarrow>R \<Longrightarrow> (P\<longrightarrow>Q)\<longrightarrow>(P\<longrightarrow>R)"
      proof -
        assume "Q\<longrightarrow>R"
        show "(P\<longrightarrow>Q)\<longrightarrow>(P\<longrightarrow>R)"
        proof (rule impI)
          assume "P\<longrightarrow>Q"
          show "P\<longrightarrow>R"
          proof (rule impI)
            assume "P"
            have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
            show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
          qed
        qed
      qed

(*3.0.9*)
      have "\<not>P \<Longrightarrow> \<not>(P\<and>Q)"
      proof -
        assume "\<not>P"
        have "P\<and>Q \<Longrightarrow> False"
        proof - 
          assume "P\<and>Q"
          have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
          show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
        qed
        show "\<not>(P\<and>Q)" using \<open>P\<and>Q \<Longrightarrow> False\<close> by (rule notI)
      qed

(*3.1.1*)
      have "P \<Longrightarrow> Q\<longrightarrow>(P\<and>Q)"
      proof -
        assume "P"
        show "Q\<longrightarrow>(P\<and>Q)"
        proof (rule impI)
          assume "Q"
          show "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
        qed
      qed

(*3.1.2*)
      have "(P\<longrightarrow>Q)\<and>(P\<longrightarrow>R) \<Longrightarrow> P\<longrightarrow>(Q\<and>R)"
      proof -
        assume "(P\<longrightarrow>Q)\<and>(P\<longrightarrow>R)"
        have "P\<longrightarrow>Q" using \<open>(P\<longrightarrow>Q)\<and>(P\<longrightarrow>R)\<close> by (rule conjunct1)
        have "P\<longrightarrow>R" using \<open>(P\<longrightarrow>Q)\<and>(P\<longrightarrow>R)\<close> by (rule conjunct2)
        show "P\<longrightarrow>(Q\<and>R)" 
        proof (rule impI)
          assume "P"
          have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
          have "R" using \<open>P\<longrightarrow>R\<close> \<open>P\<close> by (rule mp)
          show "Q\<and>R" using \<open>Q\<close> \<open>R\<close> by (rule conjI)
        qed
      qed

(*3.1.3*)
      have "P\<longrightarrow>(Q\<longrightarrow>R) \<Longrightarrow> Q\<longrightarrow>(P\<longrightarrow>R)"
      proof -
        assume "P\<longrightarrow>(Q\<longrightarrow>R)"
        show "Q\<longrightarrow>(P\<longrightarrow>R)"
        proof (rule impI)
          assume "Q"
          show "P\<longrightarrow>R"
          proof (rule impI)
            assume "P"
            have "Q\<longrightarrow>R" using \<open>P\<longrightarrow>(Q\<longrightarrow>R)\<close> \<open>P\<close> by (rule mp)
            show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
          qed
        qed
      qed

(*3.1.4*)
      have "P\<longrightarrow>Q \<Longrightarrow> (Q\<longrightarrow>R)\<longrightarrow>(P\<longrightarrow>R)"
      proof -
        assume "P\<longrightarrow>Q"
        show "(Q\<longrightarrow>R)\<longrightarrow>(P\<longrightarrow>R)"
        proof (rule impI)
          assume "Q\<longrightarrow>R"
          show "P\<longrightarrow>R"
          proof (rule impI)
            assume "P"
            have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
            show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
          qed
        qed
      qed

(*3.1.5*)
      have "P\<longrightarrow>(P\<longrightarrow>Q) \<Longrightarrow> P\<longrightarrow>Q"
      proof -
        assume "P\<longrightarrow>(P\<longrightarrow>Q)"
        show "P\<longrightarrow>Q"
        proof (rule impI)
          assume "P"
          have "P\<longrightarrow>Q" using \<open>P\<longrightarrow>(P\<longrightarrow>Q)\<close> \<open>P\<close> by (rule mp)
          show "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
        qed
      qed

(*3.1.6*)
      have "P\<longrightarrow>(Q\<longrightarrow>R) \<Longrightarrow> (P\<and>Q)\<longrightarrow>R"
      proof -
        assume "P\<longrightarrow>(Q\<longrightarrow>R)"
        show "(P\<and>Q)\<longrightarrow>R"
        proof (rule impI)
          assume "P\<and>Q"
          have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
          have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
          have "Q\<longrightarrow>R" using \<open>P\<longrightarrow>(Q\<longrightarrow>R)\<close> \<open>P\<close> by (rule mp)
          show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
        qed
      qed

(*3.1.7*)
      have "(P\<or>Q)\<longrightarrow>R \<Longrightarrow> P\<longrightarrow>R"
      proof -
        assume "(P\<or>Q)\<longrightarrow>R"
        show "P\<longrightarrow>R"
        proof (rule impI)
          assume "P"
          have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
          show "R" using \<open>(P\<or>Q)\<longrightarrow>R\<close> \<open>P\<or>Q\<close> by (rule mp)
        qed
      qed

(*3.1.8*)
      have "\<not>P \<Longrightarrow> \<not>(P\<and>Q)"
      proof -
        assume "\<not>P"
        have "P\<and>Q \<Longrightarrow> False"
        proof -
          assume "P\<and>Q"
          have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
          show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
        qed
        show "\<not>(P\<and>Q)" using \<open>P\<and>Q \<Longrightarrow> False\<close> by (rule notI)
      qed

end 

(*3.1.9*)
theorem DM1: "\<not>(P\<or>Q) \<Longrightarrow> \<not>P\<and>\<not>Q"
      proof -
        assume "\<not>(P\<or>Q)"
        have "P \<Longrightarrow> False"
        proof -
          assume "P"
          have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
          show "False" using \<open>\<not>(P\<or>Q)\<close> \<open>P\<or>Q\<close> by (rule notE)
        qed
        have "\<not>P" using \<open>P \<Longrightarrow> False\<close> by (rule notI)
        have "Q \<Longrightarrow> False"
        proof -
          assume "Q"
          have "P\<or>Q" using \<open>Q\<close> by (rule disjI2)
          show "False" using \<open>\<not>(P\<or>Q)\<close> \<open>P\<or>Q\<close> by (rule notE)
        qed
        have "\<not>Q" using \<open>Q \<Longrightarrow> False\<close> by (rule notI)
        show "\<not>P\<and>\<not>Q" using \<open>\<not>P\<close> \<open>\<not>Q\<close> by (rule conjI)
      qed

theorem DM1_: "\<not>P\<and>\<not>Q \<Longrightarrow> \<not>(P\<or>Q)"
proof - 
  assume "\<not>P\<and>\<not>Q"
  have "\<not>P" using \<open>\<not>P\<and>\<not>Q\<close> by (rule conjunct1)
  have "\<not>Q" using \<open>\<not>P\<and>\<not>Q\<close> by (rule conjunct2)
  have "P\<or>Q \<Longrightarrow> False"
  proof - 
    assume "P\<or>Q" 
    show "False" 
    proof (rule disjE[OF \<open>P\<or>Q\<close>])
      assume "P"
      show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
    next
      assume "Q"
      show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
    qed
  qed
  show "\<not>(P\<or>Q)" using \<open>P\<or>Q \<Longrightarrow> False\<close> by (rule notI)
qed

notepad
begin
(*3.1.10*)
      have "P\<longrightarrow>\<not>P \<Longrightarrow> \<not>P"
      proof -
        assume "P\<longrightarrow>\<not>P" 
        have "P \<Longrightarrow> False"
        proof -
          assume "P"
          have "\<not>P" using \<open>P\<longrightarrow>\<not>P\<close> \<open>P\<close> by (rule mp)
          show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
        qed
        show "\<not>P" using \<open>P \<Longrightarrow> False\<close> by (rule notI)
      qed

(*3.2.0.1*)
      have "P \<Longrightarrow> P"
      proof -
        assume "P"
        show "P" using \<open>P\<close> by assumption 
      qed

(*3.2.1*)
      have "(P\<and>Q)\<longrightarrow>(Q\<and>P)"
      proof (rule impI)
        assume "P\<and>Q"
        have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
        have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
        show "Q\<and>P" using \<open>Q\<close> \<open>P\<close> by (rule conjI)
      qed

(*3.2.2*)
      have "(P\<and>Q)\<longrightarrow>P"
      proof (rule impI)
        assume "P\<and>Q"
        show "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
      qed

(*3.2.3*)
      have "Q\<longrightarrow>(P\<longrightarrow>Q)"
      proof (rule impI)
        assume "Q"
        show "P\<longrightarrow>Q"
        proof (rule impI)
          assume "P"
          show "Q" using \<open>Q\<close> by assumption
        qed
      qed

(*3.2.4*)
      have "Q\<longrightarrow>(P\<longrightarrow>P)"
      proof (rule impI)
        assume "Q"
        show "P\<longrightarrow>P"
        proof (rule impI)
          assume "P"
          show "P" using \<open>P\<close> by assumption
        qed
      qed

(*3.2.5*)
      have "P\<or>\<not>P"
      proof -
        have "\<not>(P\<or>\<not>P) \<Longrightarrow> False"
        proof -
          assume "\<not>(P\<or>\<not>P)"
          have "\<not>P\<and>\<not>\<not>P" using \<open>\<not>(P\<or>\<not>P)\<close> by (rule DM1)
          have "\<not>P" using \<open>\<not>P\<and>\<not>\<not>P\<close> by (rule conjunct1)
          have "\<not>\<not>P" using \<open>\<not>P\<and>\<not>\<not>P\<close> by (rule conjunct2)
          show "False" using \<open>\<not>\<not>P\<close> \<open>\<not>P\<close> by (rule notE)
        qed
        have "\<not>\<not>(P\<or>\<not>P)" using \<open>\<not>(P\<or>\<not>P) \<Longrightarrow> False\<close> by (rule notI)
        show "P\<or>\<not>P" using \<open>\<not>\<not>(P\<or>\<not>P)\<close> by (rule notnotD)
      qed

(*3.2.6.0*)
      have "Q \<Longrightarrow> P\<longrightarrow>Q"
      proof -
        assume "Q"
        show "P\<longrightarrow>Q"
        proof (rule impI)
          assume "P"
          show "Q" using \<open>Q\<close> by assumption
        qed
      qed

(*3.2.6.1.1*)
      have "\<not>P \<Longrightarrow> P\<longrightarrow>Q"
      proof -
        assume "\<not>P"
        show "P\<longrightarrow>Q"
        proof (rule impI)
          assume "P"
          show "Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
        qed
      qed

(*3.2.6.1.2*)
      have "\<not>P \<Longrightarrow> P\<longrightarrow>Q"
      proof -
        assume "\<not>P"
        show "P\<longrightarrow>Q"
        proof (rule impI)
          assume "P"
          have "\<not>Q \<Longrightarrow> False"
          proof - 
            assume "\<not>Q"
            have "\<not>Q\<longrightarrow>P"
            proof (rule impI)
              show "P" using \<open>P\<close> by assumption
            qed 
            have "\<not>\<not>Q" using \<open>\<not>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
            have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
            show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
          qed
          have "\<not>\<not>Q" using \<open>\<not>Q \<Longrightarrow> False\<close> by (rule notI)
          show "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
        qed
      qed

(*3.2.6.2*)
      have "\<lbrakk>P\<or>Q ; Q\<longrightarrow>P\<rbrakk> \<Longrightarrow> P"
      proof -
        assume "P\<or>Q"
        assume "Q\<longrightarrow>P"
        show "P" 
        proof (rule disjE[OF \<open>P\<or>Q\<close>])
          assume "P"
          show "P" using \<open>P\<close> by assumption
        next
          assume "Q"
          show "P" using \<open>Q\<longrightarrow>P\<close> \<open>Q\<close> by (rule mp)
        qed
      qed

(*3.2.6.3*)
      have "P\<or>(P\<and>Q) \<Longrightarrow> P"
      proof -
        assume "P\<or>(P\<and>Q)"
        show "P"
        proof (rule disjE[OF \<open>P\<or>(P\<and>Q)\<close>])
          assume "P"
          show "P" using \<open>P\<close> by assumption
        next
          assume "P\<and>Q"
          show "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
        qed
      qed

(*3.2.6.4*)
      have "P\<or>Q \<Longrightarrow> Q\<or>P"
      proof -
        assume "P\<or>Q"
        show "Q\<or>P"
        proof (rule disjE[OF \<open>P\<or>Q\<close>])
          assume "P"
          show "Q\<or>P" using \<open>P\<close> by (rule disjI2)
        next
          assume "Q"
          show "Q\<or>P" using \<open>Q\<close> by (rule disjI1)
        qed
      qed

end

(*3.2.6.5*)
theorem or_self: "P\<or>P \<Longrightarrow> P"
      proof -
        assume "P\<or>P"
        show "P"
        proof (rule disjE [OF \<open>P\<or>P\<close>])
          assume "P"
          show "P" using \<open>P\<close> by assumption
        next
          assume "P"
          show "P" using \<open>P\<close> by assumption
        qed
      qed

      


(*3.2.7*)
theorem DM2: "\<not>(P\<and>Q) \<Longrightarrow> \<not>P\<or>\<not>Q"
      proof - 
        assume "\<not>(P\<and>Q)"
        have "\<not>(\<not>P\<or>\<not>Q) \<Longrightarrow> False" 
        proof -
          assume "\<not>(\<not>P\<or>\<not>Q)"
          have "\<not>\<not>P\<and>\<not>\<not>Q" using \<open>\<not>(\<not>P\<or>\<not>Q)\<close> by (rule DM1)
          have "\<not>\<not>P" using \<open>\<not>\<not>P\<and>\<not>\<not>Q\<close> by (rule conjunct1)
          have "\<not>\<not>Q" using \<open>\<not>\<not>P\<and>\<not>\<not>Q\<close> by (rule conjunct2)
          have "P" using \<open>\<not>\<not>P\<close> by (rule notnotD)
          have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
          have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
          show "False" using \<open>\<not>(P\<and>Q)\<close> \<open>P\<and>Q\<close> by (rule notE)
        qed
        have "\<not>\<not>(\<not>P\<or>\<not>Q)" using \<open>\<not>(\<not>P\<or>\<not>Q) \<Longrightarrow> False\<close> by (rule notI)
        show "\<not>P\<or>\<not>Q" using \<open>\<not>\<not>(\<not>P\<or>\<not>Q)\<close> by (rule notnotD)
      qed

theorem DM2_: "\<not>P\<or>\<not>Q \<Longrightarrow> \<not>(P\<and>Q)"
proof - 
  assume "\<not>P\<or>\<not>Q"
  have "P\<and>Q \<Longrightarrow> False"
  proof - 
    assume "P\<and>Q"
    have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
    have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
    show "False"
    proof (rule disjE[OF \<open>\<not>P\<or>\<not>Q\<close>])
      assume "\<not>P"
      show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
    next
      assume "\<not>Q"
      show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
    qed
  qed
  show "\<not>(P\<and>Q)" using \<open>P\<and>Q \<Longrightarrow> False\<close> by (rule notI)
qed

notepad
begin
(*3.3.1*)
      have "(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R) \<Longrightarrow> (P\<or>Q)\<longrightarrow>R" 
      proof -
        assume "(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R)"
        have "P\<longrightarrow>R" using \<open>(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R)\<close> by (rule conjunct1)
        have "Q\<longrightarrow>R" using \<open>(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R)\<close> by (rule conjunct2)
        show "(P\<or>Q)\<longrightarrow>R"
        proof (rule impI)
          assume "P\<or>Q"
          show "R"
          proof (rule disjE [OF \<open>P\<or>Q\<close>])
            assume "P"
            show "R" using \<open>P\<longrightarrow>R\<close> \<open>P\<close> by (rule mp)
          next
            assume "Q"
            show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
          qed
        qed
      qed
      

(*3.3.2.1*)
        have "P\<or>(Q\<or>R) \<Longrightarrow> (P\<or>Q)\<or>R"
        proof -
          assume "P\<or>(Q\<or>R)"
          show "(P\<or>Q)\<or>R"
          proof (rule disjE[OF \<open>P\<or>(Q\<or>R)\<close>])
            assume "P"
            have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
            show "(P\<or>Q)\<or>R" using \<open>P\<or>Q\<close> by (rule disjI1)
          next
            assume "Q\<or>R" 
            show "(P\<or>Q)\<or>R"
            proof (rule disjE[OF \<open>Q\<or>R\<close>])
              assume "Q"
              have "P\<or>Q" using \<open>Q\<close> by (rule disjI2)
              show "(P\<or>Q)\<or>R" using \<open>P\<or>Q\<close> by (rule disjI1)
            next
              assume "R"
              show "(P\<or>Q)\<or>R" using \<open>R\<close> by (rule disjI2)
            qed
          qed
        qed 

(*3.3.2.2*)
        have "(P\<or>Q)\<or>R \<Longrightarrow> P\<or>(Q\<or>R)"
        proof -
          assume "(P\<or>Q)\<or>R"
          show "P\<or>(Q\<or>R)"
          proof (rule disjE[OF \<open>(P\<or>Q)\<or>R\<close>])
            assume "P\<or>Q"
            show "P\<or>(Q\<or>R)"
            proof (rule disjE[OF \<open>P\<or>Q\<close>])
              assume "P"
              show "P\<or>(Q\<or>R)" using \<open>P\<close> by (rule disjI1)
            next
              assume "Q"
              have "Q\<or>R" using \<open>Q\<close> by (rule disjI1)
              show "P\<or>(Q\<or>R)" using \<open>Q\<or>R\<close> by (rule disjI2)
            qed
          next
            assume "R"
              have "Q\<or>R" using \<open>R\<close> by (rule disjI2)
              show "P\<or>(Q\<or>R)" using \<open>Q\<or>R\<close> by (rule disjI2)
            qed
          qed

(*3.3.3*)
          have "\<lbrakk>P\<or>Q ; \<not>P\<rbrakk> \<Longrightarrow> Q"
          proof -
            assume "P\<or>Q"
            assume "\<not>P"
            show "Q"
            proof (rule disjE [OF \<open>P\<or>Q\<close>])
              assume "P"
              show "Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
            next
              assume "Q"
              show "Q" using \<open>Q\<close> by assumption
            qed
          qed

(*3.3.4.1*)
          have "P\<and>(Q\<or>R) \<Longrightarrow> (P\<and>Q)\<or>(P\<and>R)"
          proof -
            assume "P\<and>(Q\<or>R)"
            have "P" using \<open>P\<and>(Q\<or>R)\<close> by (rule conjunct1)
            have "Q\<or>R" using \<open>P\<and>(Q\<or>R)\<close> by (rule conjunct2)
            show "(P\<and>Q)\<or>(P\<and>R)" 
            proof (rule disjE [OF \<open>Q\<or>R\<close>])
              assume "Q"
              have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
              show "(P\<and>Q)\<or>(P\<and>R)" using \<open>P\<and>Q\<close> by (rule disjI1)
            next
              assume "R"
              have "P\<and>R" using \<open>P\<close> \<open>R\<close> by (rule conjI)
              show "(P\<and>Q)\<or>(P\<and>R)" using \<open>P\<and>R\<close> by (rule disjI2)
            qed
          qed

(*3.3.4.2*)
          have "(P\<and>Q)\<or>(P\<and>R) \<Longrightarrow> P\<and>(Q\<or>R)"
          proof - 
            assume "(P\<and>Q)\<or>(P\<and>R)"
            show "P\<and>(Q\<or>R)"
            proof (rule disjE [OF \<open>(P\<and>Q)\<or>(P\<and>R)\<close>])
              assume "P\<and>Q"
              have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
              have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
              have "Q\<or>R" using \<open>Q\<close> by (rule disjI1)
              show "P\<and>(Q\<or>R)" using \<open>P\<close> \<open>Q\<or>R\<close> by (rule conjI)
            next
              assume "P\<and>R"
              have "P" using \<open>P\<and>R\<close> by (rule conjunct1)
              have "R" using \<open>P\<and>R\<close> by (rule conjunct2)
              have "Q\<or>R" using \<open>R\<close> by (rule disjI2)
              show "P\<and>(Q\<or>R)" using \<open>P\<close> \<open>Q\<or>R\<close> by (rule conjI)
            qed
          qed

(*3.3.5.1*)
          have "P\<or>(Q\<and>R) \<Longrightarrow> (P\<or>Q)\<and>(P\<or>R)"
          proof - 
            assume "P\<or>(Q\<and>R)"
            show "(P\<or>Q)\<and>(P\<or>R)"
            proof (rule disjE [OF \<open>P\<or>(Q\<and>R)\<close>])
              assume "P"
              have "P\<or>Q" using \<open>P\<close> by (rule disjI1)
              have "P\<or>R" using \<open>P\<close> by (rule disjI1)
              show "(P\<or>Q)\<and>(P\<or>R)" using \<open>P\<or>Q\<close> \<open>P\<or>R\<close> by (rule conjI)
            next
              assume "Q\<and>R"
              have "Q" using \<open>Q\<and>R\<close> by (rule conjunct1)
              have "R" using \<open>Q\<and>R\<close> by (rule conjunct2)
              have "P\<or>Q" using \<open>Q\<close> by (rule disjI2)
              have "P\<or>R" using \<open>R\<close> by (rule disjI2)
              show "(P\<or>Q)\<and>(P\<or>R)" using \<open>P\<or>Q\<close> \<open>P\<or>R\<close> by (rule conjI)
            qed
          qed

(*3.3.5.2*)
          have "(P\<or>Q)\<and>(P\<or>R) \<Longrightarrow> P\<or>(Q\<and>R)"
          proof - 
            assume "(P\<or>Q)\<and>(P\<or>R)"
            have "P\<or>Q" using \<open>(P\<or>Q)\<and>(P\<or>R)\<close> by (rule conjunct1)
            have "P\<or>R" using \<open>(P\<or>Q)\<and>(P\<or>R)\<close> by (rule conjunct2)
            show "P\<or>(Q\<and>R)" 
            proof (rule disjE [OF \<open>P\<or>Q\<close>])
              assume "P"
              show "P\<or>(Q\<and>R)" using \<open>P\<close> by (rule disjI1)
            next
              assume "Q"
              show "P\<or>(Q\<and>R)"
              proof (rule disjE [OF \<open>P\<or>R\<close>])
                assume "P"
                show "P\<or>(Q\<and>R)" using \<open>P\<close> by (rule disjI1)
              next
                assume "R"
                have "Q\<and>R" using \<open>Q\<close> \<open>R\<close> by (rule conjI)
                show "P\<or>(Q\<and>R)" using \<open>Q\<and>R\<close> by (rule disjI2)
              qed
            qed
          qed

(*3.3.6.1*)
          have "\<not>P\<or>Q \<Longrightarrow> P\<longrightarrow>Q"
          proof - 
            assume "\<not>P\<or>Q"
            show "P\<longrightarrow>Q"
            proof (rule disjE [OF \<open>\<not>P\<or>Q\<close>])
              assume "\<not>P"
              show "P\<longrightarrow>Q"
              proof (rule impI)
                assume "P"
                show "Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
              qed
            next
              assume "Q"
              show "P\<longrightarrow>Q"
              proof (rule impI)
                assume "P"
                show "Q" using \<open>Q\<close> by assumption
              qed
            qed
          qed
end 
(*3.3.6.2*)
theorem imp_to_or: "P\<longrightarrow>Q \<Longrightarrow> \<not>P\<or>Q"
          proof - 
            assume "P\<longrightarrow>Q"
            have "P\<and>\<not>Q \<Longrightarrow> False"
            proof - 
              assume "P\<and>\<not>Q"
              have "P" using \<open>P\<and>\<not>Q\<close> by (rule conjunct1)
              have "\<not>Q" using \<open>P\<and>\<not>Q\<close> by (rule conjunct2)
              have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
              show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
            qed
            have "\<not>(P\<and>\<not>Q)" using \<open>P\<and>\<not>Q \<Longrightarrow> False\<close> by (rule notI)
            have "\<not>P\<or>\<not>\<not>Q" using \<open>\<not>(P\<and>\<not>Q)\<close> by (rule DM2)
            show "\<not>P\<or>Q" 
            proof (rule disjE [OF \<open>\<not>P\<or>\<not>\<not>Q\<close>])
              assume "\<not>P"
              show "\<not>P\<or>Q" using \<open>\<not>P\<close> by (rule disjI1)
            next
              assume "\<not>\<not>Q"
              have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
              show "\<not>P\<or>Q" using \<open>Q\<close> by (rule disjI2)
            qed
          qed

notepad
begin
(*3.3.7*)
          have "\<not>P\<or>\<not>Q \<Longrightarrow> \<not>(P\<and>Q)"
          proof - 
            assume "\<not>P\<or>\<not>Q"
            show "\<not>(P\<and>Q)"
            proof (rule disjE [OF \<open>\<not>P\<or>\<not>Q\<close>])
              assume "\<not>P"
              have "P\<and>Q \<Longrightarrow> False"
              proof -
                assume "P\<and>Q"
                have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
                show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
              qed
              show "\<not>(P\<and>Q)" using \<open>P\<and>Q \<Longrightarrow> False\<close> by (rule notI)
            next
              assume "\<not>Q"
              have "P\<and>Q \<Longrightarrow> False"
              proof -
                assume "P\<and>Q"
                have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
                show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
              qed
              show "\<not>(P\<and>Q)" using \<open>P\<and>Q \<Longrightarrow> False\<close> by (rule notI)
            qed
          qed

(*3.3.8*)
          have "\<lbrakk>P\<longrightarrow>Q ; P\<longrightarrow>\<not>Q \<rbrakk> \<Longrightarrow> \<not>P"
          proof -
            assume "P\<longrightarrow>Q"
            assume "P\<longrightarrow>\<not>Q"
            have "P \<Longrightarrow> False"
            proof - 
              assume "P"
              have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
              have "\<not>Q" using \<open>P\<longrightarrow>\<not>Q\<close> \<open>P\<close> by (rule mp)
              show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
            qed
            show "\<not>P" using \<open>P \<Longrightarrow> False\<close> by (rule notI)
          qed
end

(*3.3.9*)
theorem lem: "P\<or>\<not>P"
          proof -
            have "\<not>(P\<or>\<not>P) \<Longrightarrow> False"
            proof - 
              assume "\<not>(P\<or>\<not>P)"
              have "\<not>P\<and>\<not>\<not>P" using \<open>\<not>(P\<or>\<not>P)\<close> by (rule DM1)
              have "\<not>P" using \<open>\<not>P\<and>\<not>\<not>P\<close> by (rule conjunct1)
              have "\<not>\<not>P" using \<open>\<not>P\<and>\<not>\<not>P\<close> by (rule conjunct2)
              show "False" using \<open>\<not>\<not>P\<close> \<open>\<not>P\<close> by (rule notE)
            qed
            have "\<not>\<not>(P\<or>\<not>P)" using \<open>\<not>(P\<or>\<not>P) \<Longrightarrow> False\<close> by (rule notI)
            show "P\<or>\<not>P" using \<open>\<not>\<not>(P\<or>\<not>P)\<close> by (rule notnotD)
          qed

notepad
begin
(*3.3.10.1*)
          have "P\<and>\<not>P \<Longrightarrow> Q"
          proof -
            assume "P\<and>\<not>P"
            have "P" using \<open>P\<and>\<not>P\<close> by (rule conjunct1)
            have "\<not>P" using \<open>P\<and>\<not>P\<close> by (rule conjunct2) 
            show "Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
          qed

(*3.3.10.2*)
          have "P\<and>\<not>P \<Longrightarrow> Q"
          proof -
            assume "P\<and>\<not>P"
            have "P" using \<open>P\<and>\<not>P\<close> by (rule conjunct1)
            have "\<not>P" using \<open>P\<and>\<not>P\<close> by (rule conjunct2)
            have "\<not>Q\<longrightarrow>P"
            proof (rule impI)
              assume "\<not>Q"
              show "P" using \<open>P\<close> by assumption
            qed
            have "\<not>\<not>Q" using \<open>\<not>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
            show "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
          qed

(*3.3.11.1*)
          have "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P"
          proof - 
            have "P\<or>\<not>P" by (rule lem)
            show "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P"
            proof (rule disjE [OF \<open>P\<or>\<not>P\<close>])
              assume "P"
              show "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P"
              proof (rule impI)
                assume "(P\<longrightarrow>Q)\<longrightarrow>P"
                show "P" using \<open>P\<close> by assumption
              qed
            next
              assume "\<not>P"
              have "P\<longrightarrow>Q"
              proof (rule impI)
                assume "P"
                have "\<not>Q\<longrightarrow>\<not>P"
                proof (rule impI)
                  assume "\<not>Q"
                  show "\<not>P" using \<open>\<not>P\<close> by assumption
                qed
                have "\<not>\<not>P" using \<open>P\<close> by (rule notnotI)
                have "\<not>\<not>Q" using \<open>\<not>Q\<longrightarrow>\<not>P\<close> \<open>\<not>\<not>P\<close> by (rule mt)
                show "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
              qed
              have "\<not>((P\<longrightarrow>Q)\<longrightarrow>P)"
              proof -
                have "(P\<longrightarrow>Q)\<longrightarrow>P \<Longrightarrow> False"
                proof - 
                  assume "(P\<longrightarrow>Q)\<longrightarrow>P"
                  have "P" using \<open>(P\<longrightarrow>Q)\<longrightarrow>P\<close> \<open>P\<longrightarrow>Q\<close> by (rule mp)
                  show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
                qed
                show "\<not>((P\<longrightarrow>Q)\<longrightarrow>P)" using \<open>(P\<longrightarrow>Q)\<longrightarrow>P \<Longrightarrow> False\<close> by (rule notI)
              qed
              show "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P"
              proof (rule impI)
                assume "(P\<longrightarrow>Q)\<longrightarrow>P" 
                show "P" using \<open>\<not>((P\<longrightarrow>Q)\<longrightarrow>P)\<close> \<open>(P\<longrightarrow>Q)\<longrightarrow>P\<close> by (rule notE)
              qed
            qed
          qed
end

(*Positive Paradox and Negative Paradox*)

theorem PP: "Q \<Longrightarrow> P\<longrightarrow>Q"
proof -
  assume "Q"
  show "P\<longrightarrow>Q"
  proof (rule impI)
    assume "P"
    show "Q" using \<open>Q\<close> by assumption
  qed
qed

theorem NP: "\<not>P \<Longrightarrow> P\<longrightarrow>Q"
proof -
  assume "\<not>P"
  have "\<not>Q\<longrightarrow>\<not>P"
  proof (rule impI) 
    assume "\<not>Q"
    show "\<not>P" using \<open>\<not>P\<close> by assumption
  qed
  show "P\<longrightarrow>Q"
  proof (rule impI)
    assume "P"
    have "\<not>\<not>P" using \<open>P\<close> by (rule notnotI)
    have "\<not>\<not>Q" using \<open>\<not>Q\<longrightarrow>\<not>P\<close> \<open>\<not>\<not>P\<close> by (rule mt)
    show "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
  qed
qed

notepad
begin


(*3.3.11.1*)
          have "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P"
          proof - 
            have "P\<or>\<not>P" by (rule lem)
            show "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P"
            proof (rule disjE [OF \<open>P\<or>\<not>P\<close>])
              assume "P"
              show "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P" using \<open>P\<close> by (rule PP)
            next
              assume "\<not>P"
              have "P\<longrightarrow>Q" using \<open>\<not>P\<close> by (rule NP)
              have "((P\<longrightarrow>Q)\<longrightarrow>P) \<longrightarrow> (\<not>(P\<longrightarrow>Q)\<or>P)" (*use 1041 imp_to_or*)
              proof (rule impI)
                assume "(P\<longrightarrow>Q)\<longrightarrow>P"
                show "\<not>(P\<longrightarrow>Q)\<or>P" using \<open>(P\<longrightarrow>Q)\<longrightarrow>P\<close> by (rule imp_to_or)
              qed
              have "\<not>\<not>(P\<longrightarrow>Q)" using \<open>P\<longrightarrow>Q\<close> by (rule notnotI)
              have "\<not>\<not>(P\<longrightarrow>Q)\<and>\<not>P" using \<open>\<not>\<not>(P\<longrightarrow>Q)\<close> \<open>\<not>P\<close> by (rule conjI)
              have "\<not>(\<not>(P\<longrightarrow>Q)\<or>P)" using \<open>\<not>\<not>(P\<longrightarrow>Q)\<and>\<not>P\<close> by (rule DM1_)
              have "\<not>((P\<longrightarrow>Q)\<longrightarrow>P)" 
                using \<open>((P\<longrightarrow>Q)\<longrightarrow>P) \<longrightarrow> (\<not>(P\<longrightarrow>Q)\<or>P)\<close>  \<open>\<not>(\<not>(P\<longrightarrow>Q)\<or>P)\<close> 
                by (rule mt)
              show "((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P" using \<open>\<not>((P\<longrightarrow>Q)\<longrightarrow>P)\<close> by (rule NP)
            qed
          qed

(*3.4.1*)
          have "P\<longrightarrow>Q \<Longrightarrow> \<not>(P\<and>\<not>Q)"
          proof - 
            assume "P\<longrightarrow>Q"
            have "\<not>P\<or>Q" using \<open>P\<longrightarrow>Q\<close> by (rule imp_to_or)
            have "\<not>P\<or>\<not>\<not>Q" 
            proof (rule disjE [OF \<open>\<not>P\<or>Q\<close>])
              assume "\<not>P"
              show "\<not>P\<or>\<not>\<not>Q" using \<open>\<not>P\<close> by (rule disjI1)
            next
              assume "Q"
              have "\<not>\<not>Q" using \<open>Q\<close> by (rule notnotI)
              show "\<not>P\<or>\<not>\<not>Q" using \<open>\<not>\<not>Q\<close> by (rule disjI2)
            qed
            show "\<not>(P\<and>\<not>Q)" using \<open>\<not>P\<or>\<not>\<not>Q\<close> by (rule DM2_)
          qed

(*3.4.2*)
          have "\<not>(P\<and>Q) \<Longrightarrow> \<not>P\<or>\<not>Q"
          proof - 
            assume "\<not>(P\<and>Q)"
            show "\<not>P\<or>\<not>Q" using \<open>\<not>(P\<and>Q)\<close> by (rule DM2)
          qed
end
(*3.4.3*)
theorem notimp_to_and: "\<not>(P\<longrightarrow>Q) \<Longrightarrow> P\<and>\<not>Q"
          proof - 
            assume "\<not>(P\<longrightarrow>Q)"
            have "\<not>(P\<and>\<not>Q) \<Longrightarrow> False"
            proof - 
              assume "\<not>(P\<and>\<not>Q)" 
              have "\<not>P\<or>\<not>\<not>Q" using \<open>\<not>(P\<and>\<not>Q)\<close> by (rule DM2)
              show "False"
              proof (rule disjE [OF \<open>\<not>P\<or>\<not>\<not>Q\<close>])
                assume "\<not>P"
                have "P\<longrightarrow>Q" using \<open>\<not>P\<close> by (rule NP)
                show "False" using \<open>\<not>(P\<longrightarrow>Q)\<close> \<open>P\<longrightarrow>Q\<close> by (rule notE)
              next
                assume "\<not>\<not>Q"
                have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
                have "P\<longrightarrow>Q" using \<open>Q\<close> by (rule PP)
                show "False" using \<open>\<not>(P\<longrightarrow>Q)\<close> \<open>P\<longrightarrow>Q\<close> by (rule notE)
              qed
            qed
            have "\<not>\<not>(P\<and>\<not>Q)" using \<open>\<not>(P\<and>\<not>Q) \<Longrightarrow> False\<close> by (rule notI)
            show "P\<and>\<not>Q" using \<open>\<not>\<not>(P\<and>\<not>Q)\<close> by (rule notnotD)
          qed

theorem and_to_notimp: "P\<and>\<not>Q \<Longrightarrow> \<not>(P\<longrightarrow>Q)"
proof - 
  assume "P\<and>\<not>Q"
  have "P" using \<open>P\<and>\<not>Q\<close> by (rule conjunct1)
  have "\<not>Q" using \<open>P\<and>\<not>Q\<close> by (rule conjunct2)
  have "(P \<longrightarrow> Q)\<longrightarrow>Q"
  proof (rule impI)
    assume "P \<longrightarrow> Q"
    show "Q" using \<open>P \<longrightarrow> Q\<close> \<open>P\<close> by (rule mp)
  qed
  show "\<not>(P \<longrightarrow> Q)" using \<open>(P \<longrightarrow> Q)\<longrightarrow>Q\<close> \<open>\<not>Q\<close> by (rule mt) 
qed

notepad
begin 
(*3.4.4*)
          have "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P)"
          proof -
            have "(P\<longrightarrow>Q)\<or>\<not>(P\<longrightarrow>Q)" by (rule lem)
            show "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P)"
            proof (rule disjE[OF \<open>(P\<longrightarrow>Q)\<or>\<not>(P\<longrightarrow>Q)\<close>])
              assume "P\<longrightarrow>Q"
              show "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P)" using \<open>P\<longrightarrow>Q\<close> by (rule disjI1)
            next
              assume "\<not>(P\<longrightarrow>Q)"
              have "P\<and>\<not>Q" using \<open>\<not>(P\<longrightarrow>Q)\<close> by (rule notimp_to_and)
              have "P" using \<open>P\<and>\<not>Q\<close> by (rule conjunct1)
              have "Q\<longrightarrow>P" using \<open>P\<close> by (rule PP)
              show "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P)" using \<open>Q\<longrightarrow>P\<close> by (rule disjI2)
            qed
          qed
(*3.4.5*)
          have "P\<longrightarrow>(Q\<or>R) \<Longrightarrow> (P\<longrightarrow>Q)\<or>(P\<longrightarrow>R)"
          proof - 
            assume "P\<longrightarrow>(Q\<or>R)"
            have "\<not>((P\<longrightarrow>Q)\<or>(P\<longrightarrow>R)) \<Longrightarrow> False"
            proof -
              assume "\<not>((P\<longrightarrow>Q)\<or>(P\<longrightarrow>R))"
              have "\<not>(P\<longrightarrow>Q)\<and>\<not>(P\<longrightarrow>R)" using \<open>\<not>((P\<longrightarrow>Q)\<or>(P\<longrightarrow>R))\<close> by (rule DM1)
              have "\<not>(P\<longrightarrow>Q)" using \<open>\<not>(P\<longrightarrow>Q)\<and>\<not>(P\<longrightarrow>R)\<close> by (rule conjunct1)
              have "\<not>(P\<longrightarrow>R)" using \<open>\<not>(P\<longrightarrow>Q)\<and>\<not>(P\<longrightarrow>R)\<close> by (rule conjunct2)
              have "P\<and>\<not>Q" using \<open>\<not>(P\<longrightarrow>Q)\<close> by (rule notimp_to_and)
              have "P\<and>\<not>R" using \<open>\<not>(P\<longrightarrow>R)\<close> by (rule notimp_to_and)
              have "P" using \<open>P\<and>\<not>Q\<close> by (rule conjunct1)
              have "Q\<or>R" using \<open>P\<longrightarrow>(Q\<or>R)\<close> \<open>P\<close> by (rule mp)
              have "\<not>Q" using \<open>P\<and>\<not>Q\<close> by (rule conjunct2)
              have "\<not>R" using \<open>P\<and>\<not>R\<close> by (rule conjunct2)
              have "\<not>Q\<and>\<not>R" using \<open>\<not>Q\<close> \<open>\<not>R\<close> by (rule conjI)
              have "\<not>(Q\<or>R)" using \<open>\<not>Q\<and>\<not>R\<close> by (rule DM1_)
              show "False" using \<open>\<not>(Q\<or>R)\<close> \<open>Q\<or>R\<close> by (rule notE)
            qed
            have "\<not>\<not>((P\<longrightarrow>Q)\<or>(P\<longrightarrow>R))" 
              using \<open>\<not>((P\<longrightarrow>Q)\<or>(P\<longrightarrow>R)) \<Longrightarrow> False\<close> by (rule notI)
            show "(P\<longrightarrow>Q)\<or>(P\<longrightarrow>R)" using \<open>\<not>\<not>((P\<longrightarrow>Q)\<or>(P\<longrightarrow>R))\<close> by (rule notnotD)
          qed

(*3.4.6*)
          have "(P\<and>Q)\<longrightarrow>\<not>Q \<Longrightarrow> P\<longrightarrow>\<not>Q"
          proof - 
            assume "(P\<and>Q)\<longrightarrow>\<not>Q"
            show "P\<longrightarrow>\<not>Q"
            proof (rule impI)
              assume "P"
              have "Q \<Longrightarrow> False"
              proof - 
                assume "Q"
                have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
                have "\<not>Q" using \<open>(P\<and>Q)\<longrightarrow>\<not>Q\<close> \<open>P\<and>Q\<close> by (rule mp)
                show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
              qed
              show "\<not>Q" using \<open>Q \<Longrightarrow> False\<close> by (rule notI)
            qed
          qed

(*3.5*)
          have "\<not>\<not>P \<Longrightarrow> P"
          proof - 
            assume "\<not>\<not>P"
            have "P\<or>\<not>P" by (rule lem)
            show "P"
            proof (rule disjE[OF \<open>P\<or>\<not>P\<close>])
              assume "P"
              show "P" using \<open>P\<close> by assumption
            next
              assume "\<not>P"
              show "P" using \<open>\<not>\<not>P\<close> \<open>\<not>P\<close> by (rule notE)
            qed
          qed

(*4.0.1*)
          have "(P\<longrightarrow>Q)\<or>\<not>(P\<longrightarrow>Q)"
          proof - 
            show "(P\<longrightarrow>Q)\<or>\<not>(P\<longrightarrow>Q)" by (rule lem)
          qed

(*4.0.4*)
          have "P \<longleftrightarrow> P"
          proof - 
            have "P\<Longrightarrow>P"
            proof - 
              assume "P"
              show "P" using \<open>P\<close> by assumption
            qed
            show "P \<longleftrightarrow> P" using \<open>P\<Longrightarrow>P\<close> \<open>P\<Longrightarrow>P\<close> by (rule iffI)
          qed

(*4.0.5*)
          have "P\<and>Q \<Longrightarrow> P\<longleftrightarrow>Q"
          proof -
            assume "P\<and>Q"
            have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
            have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2) 
            have "P\<Longrightarrow>Q"
            proof - 
              assume "P"
              show "Q" using \<open>Q\<close> by assumption
            qed
            have "Q\<Longrightarrow>P"
            proof - 
              assume "Q"
              show "P" using \<open>P\<close> by assumption
            qed
            show "P\<longleftrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> \<open>Q\<Longrightarrow>P\<close> by (rule iffI)
          qed

(*4.0.6*)
          have "\<not>P\<and>\<not>Q \<Longrightarrow> P\<longleftrightarrow>Q"
          proof - 
            assume "\<not>P\<and>\<not>Q"
            have "\<not>P" using \<open>\<not>P\<and>\<not>Q\<close> by (rule conjunct1)
            have "\<not>Q" using \<open>\<not>P\<and>\<not>Q\<close> by (rule conjunct2)
            have "P\<Longrightarrow>Q"
            proof -
              assume "P"
              show "Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
            qed
            have "Q\<Longrightarrow>P"
            proof -
              assume "Q"
              show "P" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
            qed
            show "P\<longleftrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> \<open>Q\<Longrightarrow>P\<close> by (rule iffI)
          qed

(*4.0.7*)
          have "(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R) \<Longrightarrow> (P\<or>Q)\<longrightarrow>R"
          proof - 
            assume "(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R)"
            have "P\<longrightarrow>R" using \<open>(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R)\<close> by (rule conjunct1)
            have "Q\<longrightarrow>R" using \<open>(P\<longrightarrow>R)\<and>(Q\<longrightarrow>R)\<close> by (rule conjunct2)
            show "(P\<or>Q)\<longrightarrow>R"
            proof (rule impI)
              assume "P\<or>Q"
              show "R"
              proof (rule disjE[OF \<open>P\<or>Q\<close>])
                assume "P"
                show "R" using \<open>P\<longrightarrow>R\<close> \<open>P\<close> by (rule mp)
              next
                assume "Q"
                show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
              qed
            qed
          qed

(*4.3.1*)
          have "P\<longleftrightarrow>Q \<Longrightarrow> Q\<longleftrightarrow>P"
          proof - 
            assume "P\<longleftrightarrow>Q"
            have "P\<Longrightarrow>Q" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD1)
            have "Q\<Longrightarrow>P" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD2)
            show "Q\<longleftrightarrow>P" using \<open>Q\<Longrightarrow>P\<close> \<open>P\<Longrightarrow>Q\<close> by (rule iffI)
          qed

(*4.3.2*)
          have "(Q\<longrightarrow>P)\<or>(P\<longrightarrow>R)"
          proof - 
            have "\<not>((Q\<longrightarrow>P)\<or>(P\<longrightarrow>R)) \<Longrightarrow> False"
            proof - 
              assume "\<not>((Q\<longrightarrow>P)\<or>(P\<longrightarrow>R))"
              have "\<not>(Q\<longrightarrow>P)\<and>\<not>(P\<longrightarrow>R)" 
                using \<open>\<not>((Q\<longrightarrow>P)\<or>(P\<longrightarrow>R))\<close> by (rule DM1)
              have "\<not>(Q\<longrightarrow>P)" using \<open>\<not>(Q\<longrightarrow>P)\<and>\<not>(P\<longrightarrow>R)\<close> by (rule conjunct1)
              have "\<not>(P\<longrightarrow>R)" using \<open>\<not>(Q\<longrightarrow>P)\<and>\<not>(P\<longrightarrow>R)\<close> by (rule conjunct2)
              have "Q\<and>\<not>P" using \<open>\<not>(Q\<longrightarrow>P)\<close> by (rule notimp_to_and)
              have "P\<and>\<not>R" using \<open>\<not>(P\<longrightarrow>R)\<close> by (rule notimp_to_and)
              have "\<not>P" using \<open>Q\<and>\<not>P\<close> by (rule conjunct2)
              have "P" using \<open>P\<and>\<not>R\<close> by (rule conjunct1)
              show "False" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
            qed
            have "\<not>\<not>((Q\<longrightarrow>P)\<or>(P\<longrightarrow>R))" 
              using \<open>\<not>((Q\<longrightarrow>P)\<or>(P\<longrightarrow>R)) \<Longrightarrow> False\<close> by (rule notI)
            show "(Q\<longrightarrow>P)\<or>(P\<longrightarrow>R)" using \<open>\<not>\<not>((Q\<longrightarrow>P)\<or>(P\<longrightarrow>R))\<close> by (rule notnotD)
          qed

end




(*4.3.3.0*)
theorem if_if_to_iff: "(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P) \<Longrightarrow> P\<longleftrightarrow>Q"
proof - 
  assume "(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P)"
  have "P\<longrightarrow>Q" using \<open>(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P)\<close> by (rule conjunct1)
  have "Q\<longrightarrow>P" using \<open>(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P)\<close> by (rule conjunct2)
  have "P\<Longrightarrow>Q"
  proof - 
    assume "P"
    show "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
  qed
  have "Q\<Longrightarrow>P"
  proof - 
    assume "Q"
    show "P" using \<open>Q\<longrightarrow>P\<close> \<open>Q\<close> by (rule mp)
  qed
  show "P\<longleftrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> \<open>Q\<Longrightarrow>P\<close> by (rule iffI)
qed

notepad
begin


(*4.3.3.1*)
          have "P\<longleftrightarrow>Q \<Longrightarrow> (P\<and>Q)\<or>(\<not>P\<and>\<not>Q)"
          proof - 
            assume "P\<longleftrightarrow>Q"
            have "P\<Longrightarrow>Q" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD1)
            have "P\<longrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> by (rule impI)
            have "Q\<Longrightarrow>P" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD2)
            have "Q\<longrightarrow>P" using \<open>Q\<Longrightarrow>P\<close> by (rule impI)
            have "P\<or>\<not>P" by (rule lem)
            show "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)"
            proof (rule disjE[OF \<open>P\<or>\<not>P\<close>])
              assume "P"
              have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
              have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
              show "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)" using \<open>P\<and>Q\<close> by (rule disjI1)
            next
              assume "\<not>P"
              have "\<not>Q" using \<open>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
              have "\<not>P\<and>\<not>Q" using \<open>\<not>P\<close> \<open>\<not>Q\<close> by (rule conjI)
              show "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)" using \<open>\<not>P\<and>\<not>Q\<close> by (rule disjI2)
            qed
          qed
(*4.3.3.1*)
end
theorem intro_iff1: "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q) \<Longrightarrow> P\<longleftrightarrow>Q"
          proof -
            assume "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)"
            show "P\<longleftrightarrow>Q"
            proof (rule disjE[OF \<open>(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)\<close>])
              assume "P\<and>Q"
              have "P" using \<open>P\<and>Q\<close> by (rule conjunct1)
              have "Q" using \<open>P\<and>Q\<close> by (rule conjunct2)
              have "P\<Longrightarrow>Q"
              proof - 
                assume "P"
                show "Q" using \<open>Q\<close> by assumption
              qed
              have "Q\<Longrightarrow>P"
              proof - 
                assume "Q"
                show "P" using \<open>P\<close> by assumption
              qed
              show "P\<longleftrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> \<open>Q\<Longrightarrow>P\<close> by (rule iffI)
            next
              assume "\<not>P\<and>\<not>Q"
              have "\<not>P" using \<open>\<not>P\<and>\<not>Q\<close> by (rule conjunct1)
              have "\<not>Q" using \<open>\<not>P\<and>\<not>Q\<close> by (rule conjunct2)
              have "P\<Longrightarrow>Q"
              proof - 
                assume "P"
                show "Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
              qed
              have "Q\<Longrightarrow>P"
              proof - 
                assume "Q"
                show "P" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
              qed
              show "P\<longleftrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> \<open>Q\<Longrightarrow>P\<close> by (rule iffI)
            qed
          qed 

theorem iff_to_andorand: "P\<longleftrightarrow>Q \<Longrightarrow> (P\<and>Q)\<or>(\<not>P\<and>\<not>Q)"
proof - 
  assume "P\<longleftrightarrow>Q"
  have "P\<Longrightarrow>Q" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD1)
  have "P\<longrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> by (rule impI)
  have "Q\<Longrightarrow>P" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD2)
  have "Q\<longrightarrow>P" using \<open>Q\<Longrightarrow>P\<close> by (rule impI)
  have "P\<or>\<not>P" by (rule lem)
  show "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)"
  proof (rule disjE[OF \<open>P\<or>\<not>P\<close>])
    assume "P"
    have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
    have "P\<and>Q" using \<open>P\<close> \<open>Q\<close> by (rule conjI)
    show "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)" using \<open>P\<and>Q\<close> by (rule disjI1)
  next
    assume "\<not>P"
    have "\<not>Q" using \<open>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
    have "\<not>P\<and>\<not>Q" using \<open>\<not>P\<close> \<open>\<not>Q\<close> by (rule conjI)  
    show "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)" using \<open>\<not>P\<and>\<not>Q\<close> by (rule disjI2)
  qed
qed

notepad
begin 
(*4.3.4*)
          have "\<not>(P\<longleftrightarrow>P) \<Longrightarrow> Q\<and>\<not>Q"
          proof - 
            assume "\<not>(P\<longleftrightarrow>P)"
            have "(P\<longrightarrow>P)\<and>(P\<longrightarrow>P) \<Longrightarrow> P\<longleftrightarrow>P" by (rule if_if_to_iff)
            have "(P\<longrightarrow>P)\<and>(P\<longrightarrow>P) \<longrightarrow> P\<longleftrightarrow>P" 
              using \<open>(P\<longrightarrow>P)\<and>(P\<longrightarrow>P) \<Longrightarrow> P\<longleftrightarrow>P\<close> by (rule impI)
            have "\<not>((P\<longrightarrow>P)\<and>(P\<longrightarrow>P))" 
              using \<open>(P\<longrightarrow>P)\<and>(P\<longrightarrow>P) \<longrightarrow> P\<longleftrightarrow>P\<close> \<open>\<not>(P\<longleftrightarrow>P)\<close> by (rule mt)
            have "\<not>(P\<longrightarrow>P)\<or>\<not>(P\<longrightarrow>P)" 
              using \<open>\<not>((P\<longrightarrow>P)\<and>(P\<longrightarrow>P))\<close> by (rule DM2)
            have "\<not>(P\<longrightarrow>P)" using \<open>\<not>(P\<longrightarrow>P)\<or>\<not>(P\<longrightarrow>P)\<close> by (rule or_self)
            have "P\<and>\<not>P" using \<open>\<not>(P\<longrightarrow>P)\<close> by (rule notimp_to_and)
            have "P" using \<open>P\<and>\<not>P\<close> by (rule conjunct1)  
            have "\<not>P" using \<open>P\<and>\<not>P\<close> by (rule conjunct2)
            show "Q\<and>\<not>Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
          qed

(*4.3.5*)
          have "\<lbrakk>P\<longleftrightarrow>Q;Q\<longleftrightarrow>R\<rbrakk>\<Longrightarrow>P\<longleftrightarrow>R"
          proof - 
            assume "P\<longleftrightarrow>Q"
            assume "Q\<longleftrightarrow>R"
            have "P\<Longrightarrow>Q" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD1)
            have "P\<longrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> by (rule impI)
            have "Q\<Longrightarrow>P" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD2)
            have "Q\<longrightarrow>P" using \<open>Q\<Longrightarrow>P\<close> by (rule impI)
            have "Q\<Longrightarrow>R" using \<open>Q\<longleftrightarrow>R\<close> by (rule iffD1)
            have "Q\<longrightarrow>R" using \<open>Q\<Longrightarrow>R\<close> by (rule impI)
            have "R\<Longrightarrow>Q" using \<open>Q\<longleftrightarrow>R\<close> by (rule iffD2)
            have "R\<longrightarrow>Q" using \<open>R\<Longrightarrow>Q\<close> by (rule impI)
            have "P\<Longrightarrow>R"
            proof -
              assume "P"
              have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
              show "R" using \<open>Q\<longrightarrow>R\<close> \<open>Q\<close> by (rule mp)
            qed
            have "R\<Longrightarrow>P"
            proof -
              assume "R"
              have "Q" using \<open>R\<longrightarrow>Q\<close> \<open>R\<close> by (rule mp)
              show "P" using \<open>Q\<longrightarrow>P\<close> \<open>Q\<close> by (rule mp)
            qed
            show "P\<longleftrightarrow>R" 
              using \<open>P\<Longrightarrow>R\<close> \<open>R\<Longrightarrow>P\<close> by (rule iffI)
          qed

(*4.3.6.1*)
          have "\<not>(P\<longleftrightarrow>Q) \<Longrightarrow> P\<longleftrightarrow>\<not>Q"
          proof - 
            assume "\<not>(P\<longleftrightarrow>Q)"
            have "(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P) \<Longrightarrow> P\<longleftrightarrow>Q" by (rule if_if_to_iff)
            have "(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P) \<longrightarrow> P\<longleftrightarrow>Q" 
              using \<open>(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P) \<Longrightarrow> P\<longleftrightarrow>Q\<close> by (rule impI)
            have "\<not>((P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P))"
              using \<open>(P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P) \<longrightarrow> P\<longleftrightarrow>Q\<close> \<open>\<not>(P\<longleftrightarrow>Q)\<close> by (rule mt)
            have "\<not>(P\<longrightarrow>Q)\<or>\<not>(Q\<longrightarrow>P)" 
              using \<open>\<not>((P\<longrightarrow>Q)\<and>(Q\<longrightarrow>P))\<close> by (rule DM2)
            show "P\<longleftrightarrow>\<not>Q" 
            proof (rule disjE[OF \<open>\<not>(P\<longrightarrow>Q)\<or>\<not>(Q\<longrightarrow>P)\<close>])
              assume "\<not>(P\<longrightarrow>Q)"
              have "P\<and>\<not>Q" using \<open>\<not>(P\<longrightarrow>Q)\<close> by (rule notimp_to_and)
              have "P" using \<open>P\<and>\<not>Q\<close> by (rule conjunct1)
              have "\<not>Q" using \<open>P\<and>\<not>Q\<close> by (rule conjunct2)
              have "P\<Longrightarrow>\<not>Q" 
              proof - 
                assume "P"
                show "\<not>Q" using \<open>\<not>Q\<close> by assumption
              qed
              have "\<not>Q\<Longrightarrow>P" 
              proof - 
                assume "\<not>Q"
                show "P" using \<open>P\<close> by assumption
              qed
              show "P\<longleftrightarrow>\<not>Q" 
                using \<open>P\<Longrightarrow>\<not>Q\<close> \<open>\<not>Q\<Longrightarrow>P\<close> by (rule iffI)
            next
              assume "\<not>(Q\<longrightarrow>P)"
              have "Q\<and>\<not>P" using \<open>\<not>(Q\<longrightarrow>P)\<close> by (rule notimp_to_and)
              have "Q" using \<open>Q\<and>\<not>P\<close> by (rule conjunct1)
              have "\<not>P" using \<open>Q\<and>\<not>P\<close> by (rule conjunct2)
              have "P \<Longrightarrow> \<not>Q"
              proof - 
                assume "P"
                show "\<not>Q" using \<open>\<not>P\<close> \<open>P\<close> by (rule notE)
              qed
              have "\<not>Q \<Longrightarrow> P"
              proof - 
                assume "\<not>Q"
                show "P" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
              qed
              show "P\<longleftrightarrow>\<not>Q" 
                using \<open>P\<Longrightarrow>\<not>Q\<close> \<open>\<not>Q\<Longrightarrow>P\<close> by (rule iffI)
            qed
          qed

(*4.3.6.2*)
          have "P\<longleftrightarrow>\<not>Q \<Longrightarrow> \<not>(P\<longleftrightarrow>Q)"
          proof - 
            assume "P\<longleftrightarrow>\<not>Q"
            have "P\<Longrightarrow>\<not>Q" using \<open>P\<longleftrightarrow>\<not>Q\<close> by (rule iffD1)
            have "P\<longrightarrow>\<not>Q" using \<open>P\<Longrightarrow>\<not>Q\<close> by (rule impI)
            have "\<not>Q\<Longrightarrow>P" using \<open>P\<longleftrightarrow>\<not>Q\<close> by (rule iffD2)
            have "\<not>Q\<longrightarrow>P" using \<open>\<not>Q\<Longrightarrow>P\<close> by (rule impI)
            have "P\<longleftrightarrow>Q \<Longrightarrow> False"
            proof - 
              assume "P\<longleftrightarrow>Q"
              have "P\<Longrightarrow>Q" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD1)
              have "P\<longrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> by (rule impI)
              have "Q\<Longrightarrow>P" using \<open>P\<longleftrightarrow>Q\<close> by (rule iffD2)
              have "Q\<longrightarrow>P" using \<open>Q\<Longrightarrow>P\<close> by (rule impI)
              have "P\<or>\<not>P" by (rule lem)
              show "False"
              proof (rule disjE[OF \<open>P\<or>\<not>P\<close>])
                assume "P"
                have "Q" using \<open>P\<longrightarrow>Q\<close> \<open>P\<close> by (rule mp)
                have "\<not>Q" using \<open>P\<longrightarrow>\<not>Q\<close> \<open>P\<close> by (rule mp)
                show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
              next
                assume "\<not>P"
                have "\<not>Q" using \<open>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
                have "\<not>\<not>Q" using \<open>\<not>Q\<longrightarrow>P\<close> \<open>\<not>P\<close> by (rule mt)
                have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
                show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
              qed
            qed
            show "\<not>(P\<longleftrightarrow>Q)" using \<open>P\<longleftrightarrow>Q \<Longrightarrow> False\<close> by (rule notI)
          qed

(*4.0.0*)
          have "P\<Longrightarrow> P\<or>Q\<or>R"
          proof - 
            assume "P"
            show "P\<or>Q\<or>R" using \<open>P\<close> by (rule disjI1)
          qed


(*4.3.7*)
          have "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)"
          proof - 
            have "P\<or>\<not>P" by (rule lem)
            have "Q\<or>\<not>Q" by (rule lem)
            have "R\<or>\<not>R" by (rule lem)
            show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
            proof (rule disjE[OF \<open>P\<or>\<not>P\<close>])
              assume "P"
              show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
              proof (rule disjE[OF \<open>Q\<or>\<not>Q\<close>])
                assume "Q"
                have "P\<Longrightarrow>Q"
                proof - 
                  assume "P"
                  show "Q" using \<open>Q\<close> by assumption
                qed
                have "Q\<Longrightarrow>P"
                proof - 
                  assume "Q"
                  show "P" using \<open>P\<close> by assumption
                qed
                have "P\<longleftrightarrow>Q" using \<open>P\<Longrightarrow>Q\<close> \<open>Q\<Longrightarrow>P\<close> by (rule iffI)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" using \<open>P\<longleftrightarrow>Q\<close> by (rule disjI1)
              next
                assume "\<not>Q"
              show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
              proof (rule disjE[OF \<open>R\<or>\<not>R\<close>])
                assume "R"
                have "P\<Longrightarrow>R"
                proof - 
                  assume "P"
                  show "R" using \<open>R\<close> by assumption
                qed
                have "R\<Longrightarrow>P"
                proof - 
                  assume "R"
                  show "P" using \<open>P\<close> by assumption
                qed
                have "P\<longleftrightarrow>R" using \<open>P\<Longrightarrow>R\<close> \<open>R\<Longrightarrow>P\<close> by (rule iffI)
                have "(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" using \<open>P\<longleftrightarrow>R\<close> by (rule disjI2)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
                  using \<open>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close> by (rule disjI2)
              next
                assume "\<not>R"
                have "\<not>Q\<and>\<not>R" using \<open>\<not>Q\<close> \<open>\<not>R\<close> by (rule conjI)
                have "(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)" using \<open>\<not>Q\<and>\<not>R\<close> by (rule disjI2)
                have "Q\<longleftrightarrow>R" using \<open>(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)\<close> by (rule intro_iff1)
                have "(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" using \<open>Q\<longleftrightarrow>R\<close> by (rule disjI1)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
                  using \<open>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close> by (rule disjI2)
              qed
            qed
          next
            assume "\<not>P"
            show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
            proof (rule disjE[OF \<open>Q\<or>\<not>Q\<close>])
              assume "Q"
              show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
              proof (rule disjE[OF \<open>R\<or>\<not>R\<close>])
                assume "R"
                have "Q\<and>R" using \<open>Q\<close> \<open>R\<close> by (rule conjI)
                have "(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)" using \<open>Q\<and>R\<close> by (rule disjI1)
                have "Q\<longleftrightarrow>R" using \<open>(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)\<close> by (rule intro_iff1)
                have "(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" using \<open>Q\<longleftrightarrow>R\<close> by (rule disjI1)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
                  using \<open>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close> by (rule disjI2)
              next
                assume "\<not>R"
                have "\<not>P\<and>\<not>R" using \<open>\<not>P\<close> \<open>\<not>R\<close> by (rule conjI)
                have "(P\<and>R)\<or>(\<not>P\<and>\<not>R)" using \<open>\<not>P\<and>\<not>R\<close> by (rule disjI2)
                have "P\<longleftrightarrow>R" using \<open>(P\<and>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule intro_iff1)
                have "(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" using \<open>P\<longleftrightarrow>R\<close> by (rule disjI2)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
                  using \<open>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close> by (rule disjI2)
              qed
            next
              assume "\<not>Q"
              show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
              proof (rule disjE[OF \<open>R\<or>\<not>R\<close>])
                assume "R"
                have "\<not>P\<and>\<not>Q" using \<open>\<not>P\<close> \<open>\<not>Q\<close> by (rule conjI)
                have "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)" using \<open>\<not>P\<and>\<not>Q\<close> by (rule disjI2)
                have "P\<longleftrightarrow>Q" using \<open>(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)\<close> by (rule intro_iff1)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
                  using \<open>P\<longleftrightarrow>Q\<close> by (rule disjI1)
              next
                assume "\<not>R"
                have "\<not>Q\<and>\<not>R" using \<open>\<not>Q\<close> \<open>\<not>R\<close> by (rule conjI)
                have "(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)" using \<open>\<not>Q\<and>\<not>R\<close> by (rule disjI2)
                have "Q\<longleftrightarrow>R" using \<open>(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)\<close> by (rule intro_iff1)
                have "(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" using \<open>Q\<longleftrightarrow>R\<close> by (rule disjI1)
                show "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)" 
                  using \<open>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close> by (rule disjI2)
              qed
            qed
          qed
        qed

(*4.3.8*)
        have "R\<or>((Q\<longrightarrow>R)\<longrightarrow>P) \<Longrightarrow> R\<or>((\<not>Q\<or>R)\<longrightarrow>P)"
        proof -
          assume "R\<or>((Q\<longrightarrow>R)\<longrightarrow>P)"
          show "R\<or>((\<not>Q\<or>R)\<longrightarrow>P)"
          proof (rule disjE[OF \<open>R\<or>((Q\<longrightarrow>R)\<longrightarrow>P)\<close>])
            assume "R"
            show "R\<or>((\<not>Q\<or>R)\<longrightarrow>P)" using \<open>R\<close> by (rule disjI1)
          next
            assume "(Q\<longrightarrow>R)\<longrightarrow>P"
            have "\<not>(Q\<longrightarrow>R)\<or>P" using \<open>(Q\<longrightarrow>R)\<longrightarrow>P\<close> by (rule imp_to_or)
            show "R\<or>((\<not>Q\<or>R)\<longrightarrow>P)"
            proof (rule disjE[OF \<open>\<not>(Q\<longrightarrow>R)\<or>P\<close>])
              assume "\<not>(Q\<longrightarrow>R)"
              have "Q\<and>\<not>R" using \<open>\<not>(Q\<longrightarrow>R)\<close> by (rule notimp_to_and)
              have "Q" using \<open>Q\<and>\<not>R\<close> by (rule conjunct1)
              have "\<not>\<not>Q" using \<open>Q\<close> by (rule notnotI)
              have "\<not>R" using \<open>Q\<and>\<not>R\<close> by (rule conjunct2)
              have "\<not>\<not>Q\<and>\<not>R" using \<open>\<not>\<not>Q\<close> \<open>\<not>R\<close> by (rule conjI)
              have "\<not>(\<not>Q\<or>R)" using \<open>\<not>\<not>Q\<and>\<not>R\<close> by (rule DM1_)
              have "(\<not>Q\<or>R)\<longrightarrow>P" using \<open>\<not>(\<not>Q\<or>R)\<close> by (rule NP)
              show "R\<or>((\<not>Q\<or>R)\<longrightarrow>P)" using \<open>(\<not>Q\<or>R)\<longrightarrow>P\<close> by (rule disjI2)
            next
              assume "P"
              have "(\<not>Q\<or>R)\<longrightarrow>P" using \<open>P\<close> by (rule PP)
              show "R\<or>((\<not>Q\<or>R)\<longrightarrow>P)" using \<open>(\<not>Q\<or>R)\<longrightarrow>P\<close> by (rule disjI2)
            qed
          qed
        qed

(*4.3.9
((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P
see Line 1194
*)

(*4.3.10*)
        have "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P) \<Longrightarrow> (P\<or>\<not>P)\<or>(Q\<or>\<not>Q)"
        proof -
          assume "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P)"
          show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)"
          proof (rule disjE[OF \<open>(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>P)\<close>])
            assume "P\<longrightarrow>Q"
            have "\<not>P\<or>Q" using \<open>P\<longrightarrow>Q\<close> by (rule imp_to_or)
            show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)"
            proof (rule disjE[OF \<open>\<not>P\<or>Q\<close>])
              assume "\<not>P"
              have "P\<or>\<not>P" using \<open>\<not>P\<close> by (rule disjI2)
              show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)" using \<open>P\<or>\<not>P\<close> by (rule disjI1)
            next
              assume "Q"
              have "Q\<or>\<not>Q" using \<open>Q\<close> by (rule disjI1)
              show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)" using \<open>Q\<or>\<not>Q\<close> by (rule disjI2)
            qed
          next
            assume "Q\<longrightarrow>P"
            have "\<not>Q\<or>P" using \<open>Q\<longrightarrow>P\<close> by (rule imp_to_or)
            show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)"
            proof (rule disjE[OF \<open>\<not>Q\<or>P\<close>])
              assume "\<not>Q"
              have "Q\<or>\<not>Q" using \<open>\<not>Q\<close> by (rule disjI2)
              show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)" using \<open>Q\<or>\<not>Q\<close> by (rule disjI2)
            next
              assume "P"
              have "P\<or>\<not>P" using \<open>P\<close> by (rule disjI1)
              show "(P\<or>\<not>P)\<or>(Q\<or>\<not>Q)" using \<open>P\<or>\<not>P\<close> by (rule disjI1)
            qed
          qed
        qed

(*4.3.11
P\<longleftrightarrow>Q \<Longrightarrow> (P\<and>Q)\<or>(\<not>P\<and>\<not>Q)"
see Line 1555
*)

(*4.3.11*)
        have "P\<or>(Q\<and>\<not>Q) \<Longrightarrow> P"
        proof - 
          assume "P\<or>(Q\<and>\<not>Q)"
          show "P"
          proof (rule disjE[OF \<open>P\<or>(Q\<and>\<not>Q)\<close>])
            assume "P"
            show "P" using \<open>P\<close> by assumption
          next
            assume "Q\<and>\<not>Q"
            have "Q" using \<open>Q\<and>\<not>Q\<close> by (rule conjunct1)
            have "\<not>Q" using \<open>Q\<and>\<not>Q\<close> by (rule conjunct2)
            have "\<not>P\<longrightarrow>Q"
            proof (rule impI) 
              assume "\<not>P"
              show "Q" using \<open>Q\<close> by assumption
            qed
            have "\<not>\<not>P" using \<open>\<not>P\<longrightarrow>Q\<close> \<open>\<not>Q\<close> by (rule mt)
            show "P" using \<open>\<not>\<not>P\<close> by (rule notnotD)
          qed
        qed

(*4.5.0*)
        have "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>R)"
        proof - 
          have "Q\<or>\<not>Q" by (rule lem)
          show "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>R)"
          proof (rule disjE[OF \<open>Q\<or>\<not>Q\<close>])
            assume "Q"
            have "P\<longrightarrow>Q" using \<open>Q\<close> by (rule PP)
            show "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>R)" using \<open>P\<longrightarrow>Q\<close> by (rule disjI1)
          next
            assume "\<not>Q"
            have "Q\<longrightarrow>R" using \<open>\<not>Q\<close> by (rule NP)
            show "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>R)" using \<open>Q\<longrightarrow>R\<close> by (rule disjI2)
          qed
        qed

(*4.5.1*)
        have "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>R) \<Longrightarrow> Q\<or>\<not>Q"
        proof - 
          assume "(P\<longrightarrow>Q)\<or>(Q\<longrightarrow>R)"
          have "\<not>(Q\<or>\<not>Q) \<Longrightarrow> False"
          proof - 
            assume "\<not>(Q\<or>\<not>Q)"
            have "\<not>Q\<and>\<not>\<not>Q" using \<open>\<not>(Q\<or>\<not>Q)\<close> by (rule DM1)
            have "\<not>Q" using \<open>\<not>Q\<and>\<not>\<not>Q\<close> by (rule conjunct1)
            have "\<not>\<not>Q" using \<open>\<not>Q\<and>\<not>\<not>Q\<close> by (rule conjunct2)
            have "Q" using \<open>\<not>\<not>Q\<close> by (rule notnotD)
            show "False" using \<open>\<not>Q\<close> \<open>Q\<close> by (rule notE)
          qed
          have "\<not>\<not>(Q\<or>\<not>Q)" using \<open>\<not>(Q\<or>\<not>Q) \<Longrightarrow> False\<close> by (rule notI)
          show "Q\<or>\<not>Q" using \<open>\<not>\<not>(Q\<or>\<not>Q)\<close> by (rule notnotD)
        qed

(*4.5.2*)
        have "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R) \<Longrightarrow> (P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
        proof - 
          assume "(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)"
          show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
          proof (rule disjE [OF \<open>(P\<longleftrightarrow>Q)\<or>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close>])
            assume "(P\<longleftrightarrow>Q)"
            have "(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)" using \<open>(P\<longleftrightarrow>Q)\<close> by (rule iff_to_andorand)
            show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
            proof (rule disjE[OF \<open>(P\<and>Q)\<or>(\<not>P\<and>\<not>Q)\<close>])
              assume "P\<and>Q"
              show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                using \<open>P\<and>Q\<close> by (rule disjI1)
            next
              assume "\<not>P\<and>\<not>Q"
              have "(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                using \<open>\<not>P\<and>\<not>Q\<close> by (rule disjI1)
              have "(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                using \<open>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
              have "(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                using \<open>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2) 
              show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                using \<open>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
            qed
          next
            assume "(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)"
            show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
            proof (rule disjE [OF \<open>(Q\<longleftrightarrow>R)\<or>(P\<longleftrightarrow>R)\<close>])
              assume "Q\<longleftrightarrow>R"
              have "(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)" using \<open>(Q\<longleftrightarrow>R)\<close> by (rule iff_to_andorand)
              show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
              proof (rule disjE[OF \<open>(Q\<and>R)\<or>(\<not>Q\<and>\<not>R)\<close>])
                assume "Q\<and>R"
                have "(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                  using \<open>Q\<and>R\<close> by (rule disjI1)
                have "(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                  using \<open>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2) 
                show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                  using \<open>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                next
                  assume "\<not>Q\<and>\<not>R"
                  have "(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                    using \<open>\<not>Q\<and>\<not>R\<close> by (rule disjI1)
                  have "(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                    using \<open>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                  have "(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                    using \<open>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                  have "(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                    using \<open>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2) 
                  show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                    using \<open>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                qed
                next
                  assume "P\<longleftrightarrow>R"
                  have "(P\<and>R)\<or>(\<not>P\<and>\<not>R)" using \<open>(P\<longleftrightarrow>R)\<close> by (rule iff_to_andorand)
                  show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                  proof (rule disjE[OF \<open>(P\<and>R)\<or>(\<not>P\<and>\<not>R)\<close>])
                    assume "P\<and>R"
                    have "(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                      using \<open>P\<and>R\<close> by (rule disjI1)
                    show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                      using \<open>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                  next
                    assume "\<not>P\<and>\<not>R"
                    have "(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                      using \<open>\<not>P\<and>\<not>R\<close> by (rule disjI2)
                    have "(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                      using \<open>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                    have "(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)" 
                      using \<open>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                    have "(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                      using \<open>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2) 
                    show "(P\<and>Q)\<or>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)"
                      using \<open>(P\<and>R)\<or>(Q\<and>R)\<or>(\<not>P\<and>\<not>Q)\<or>(\<not>Q\<and>\<not>R)\<or>(\<not>P\<and>\<not>R)\<close> by (rule disjI2)
                  qed
                qed
              qed
            qed

(*6.2*)
            have "\<lbrakk>\<forall>x. F x \<longrightarrow> G x ; F a\<rbrakk> \<Longrightarrow> G a"
            proof - 
              assume "\<forall>x. F x \<longrightarrow> G x"
              assume "F a"
              have "F a \<longrightarrow> G a" using \<open>\<forall>x. F x \<longrightarrow> G x\<close> by (rule allE)
              show "G a" using \<open>F a \<longrightarrow> G a\<close> \<open>F a\<close> by (rule mp)
            qed

(*6.3.1*)
            have "\<lbrakk>\<forall>x. F x ; \<forall>x. G x\<rbrakk> \<Longrightarrow> F a \<and> G a"
            proof - 
              assume "\<forall>x. F x"
              assume "\<forall>x. G x"
              have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
              have "G a" using \<open>\<forall>x. G x\<close> by (rule allE)
              show "F a \<and> G a" using \<open>F a\<close> \<open>G a\<close> by (rule conjI)
            qed

(*6.3.2*)
            have "\<forall>x. \<not> F x \<Longrightarrow> F a \<longrightarrow> P"
            proof - 
              assume "\<forall>x. \<not> F x" 
              have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
              show "F a \<longrightarrow> P" using \<open>\<not> F a\<close> by (rule NP)
            qed
(*6.3.3*)
            have "\<lbrakk>\<forall>x. F x \<longrightarrow> G x ; \<not> G a\<rbrakk> \<Longrightarrow> \<not> F a"
            proof - 
              assume "\<forall>x. F x \<longrightarrow> G x"
              assume "\<not> G a"
              have "F a \<longrightarrow> G a" using \<open>\<forall>x. F x \<longrightarrow> G x\<close> by (rule allE)
              show "\<not> F a" using \<open>F a \<longrightarrow> G a\<close> \<open>\<not> G a\<close> by (rule mt)
            qed

(*6.3.4*)
            have "\<lbrakk>\<forall>x. F x \<longrightarrow> G x ; \<not> G a\<rbrakk> \<Longrightarrow> \<not>(\<forall>x. F x)"
            proof -
              assume "\<forall>x. F x \<longrightarrow> G x"
              assume "\<not> G a"
              have "F a \<longrightarrow> G a" using \<open>\<forall>x. F x \<longrightarrow> G x\<close> by (rule allE)
              have "\<forall>x. F x \<Longrightarrow> False"
              proof - 
                assume "\<forall>x. F x"
                have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
                have "G a" using \<open>F a \<longrightarrow> G a\<close> \<open>F a\<close> by (rule mp)
                show "False" using \<open>\<not> G a\<close> \<open>G a\<close> by (rule notE)
              qed
              show "\<not>(\<forall>x. F x)" using \<open>\<forall>x. F x \<Longrightarrow> False\<close> by (rule notI)
            qed

(*6.3.5*)
            have "\<forall>x. \<not> F x \<Longrightarrow> \<not>(\<forall>x. F x)"
            proof - 
              assume "\<forall>x. \<not> F x"
              have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
              have "(\<forall>x. F x) \<longrightarrow> F a"
              proof (rule impI)
                assume "\<forall>x. F x"
                show "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
              qed
              show "\<not>(\<forall>x. F x)" using \<open>(\<forall>x. F x) \<longrightarrow> F a\<close> \<open>\<not> F a\<close> by (rule mt)
            qed

(*6.3.6*)
            have "\<not>(\<forall>x. (F x \<and> \<not> F x))"
            proof - 
              have "\<forall>x. (F x \<and> \<not> F x) \<Longrightarrow> False"
              proof -
                assume "\<forall>x. (F x \<and> \<not> F x)"
                have "F a \<and> \<not> F a" using \<open>\<forall>x. (F x \<and> \<not> F x)\<close> by (rule allE)
                have "\<not> F a" using \<open>F a \<and> \<not> F a\<close> by (rule conjunct2)
                have "F a" using \<open>F a \<and> \<not> F a\<close> by (rule conjunct1)
                show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
              qed
              show "\<not>(\<forall>x. (F x \<and> \<not> F x))" 
                using \<open>\<forall>x. (F x \<and> \<not> F x) \<Longrightarrow> False\<close> by (rule notI)
            qed

(*6.4.0.1*)
            have "\<lbrakk>\<forall>x. F x \<longrightarrow> G x ; \<forall>x. G x \<longrightarrow> H x\<rbrakk> \<Longrightarrow> \<forall>x. F x \<longrightarrow> H x"
            proof - 
              assume "\<forall>x. F x \<longrightarrow> G x"
              assume "\<forall>x. G x \<longrightarrow> H x"
              show "\<forall>x. F x \<longrightarrow> H x"
              proof (rule allI)
              fix a 
              have "F a \<longrightarrow> G a" using \<open>\<forall>x. F x \<longrightarrow> G x\<close> by (rule allE)
              have "G a \<longrightarrow> H a" using \<open>\<forall>x. G x \<longrightarrow> H x\<close> by (rule allE)
              show "F a \<longrightarrow> H a"
              proof (rule impI)
                assume "F a"
                have "G a" using \<open>F a \<longrightarrow> G a\<close> \<open>F a\<close> by (rule mp)
                show "H a" using \<open>G a \<longrightarrow> H a\<close> \<open>G a\<close> by (rule mp)
              qed
            qed
          qed

(*6.4.0.2*)

          have "\<forall>x. \<not> F x \<Longrightarrow> (\<forall>x. F x \<longrightarrow> G x)\<and>(\<forall>x. F x \<longrightarrow> \<not> G x)"
          proof - 
            assume "\<forall>x. \<not>F x"
            have "\<forall>x. F x \<longrightarrow> G x"
            proof (rule allI)
              fix a
              have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
              show "F a \<longrightarrow> G a" using \<open>\<not> F a\<close> by (rule NP)
            qed
            have "\<forall>x. F x \<longrightarrow> \<not> G x"
            proof (rule allI)
              fix a
              have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
              show "F a \<longrightarrow> \<not> G a" using \<open>\<not> F a\<close> by (rule NP)
            qed
            show "(\<forall>x. F x \<longrightarrow> G x)\<and>(\<forall>x. F x \<longrightarrow> \<not> G x)" 
              using \<open>(\<forall>x. F x \<longrightarrow> G x)\<close> \<open>(\<forall>x. F x \<longrightarrow> \<not> G x)\<close> by (rule conjI)
          qed              

(*6.4.0.3*)
          have "\<forall>x. F x \<Longrightarrow> \<forall>y. F y"
          proof - 
            assume "\<forall>x. F x"
            show "\<forall>y. F y"
            proof (rule allI)
              fix a
              show "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
            qed
          qed

(*6.4.0.4*)
          have "(\<forall>x. F x) \<longrightarrow> (\<forall>y. F y)"
          proof (rule impI) 
            assume "\<forall>x. F x"
            show "\<forall>y. F y"
            proof (rule allI)
            fix a
            show "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
            qed
          qed

(*6.5.1*)
          have "\<forall>x.(F x \<longrightarrow> G x) \<Longrightarrow> (\<forall>x. F x) \<longrightarrow> (\<forall>x. G x)"
          proof -
            assume "\<forall>x.(F x \<longrightarrow> G x)"
            show "(\<forall>x. F x) \<longrightarrow> (\<forall>x. G x)"
            proof (rule impI)
              assume "\<forall>x. F x"
              show "\<forall>x. G x"
              proof (rule allI)
              fix a
              have "F a \<longrightarrow> G a" using \<open>\<forall>x.(F x \<longrightarrow> G x)\<close> by (rule allE)
              have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
              show "G a" using \<open>F a \<longrightarrow> G a\<close> \<open>F a\<close> by (rule mp) 
            qed
          qed
        qed

(*6.5.2*)
        have "\<forall>x.(F x \<longrightarrow> G x) \<Longrightarrow> (\<forall>x.\<not> G x) \<longrightarrow> (\<forall>x.\<not> F x)"
        proof - 
          assume "\<forall>x.(F x \<longrightarrow> G x)"
          show "(\<forall>x.\<not> G x) \<longrightarrow> (\<forall>x.\<not> F x)"
          proof (rule impI)
            assume "\<forall>x.\<not> G x"
            show "\<forall>x.\<not> F x"
            proof (rule allI)
              fix a
              have "F a \<longrightarrow> G a" using \<open>\<forall>x.(F x \<longrightarrow> G x)\<close> by (rule allE)
              have "\<not> G a" using \<open>\<forall>x.\<not> G x\<close> by (rule allE)
              show "\<not> F a" using \<open>F a \<longrightarrow> G a\<close> \<open>\<not> G a\<close> by (rule mt)
            qed
          qed
        qed

(*6.5.3.1*)
        have "(\<forall>x. F x) \<and> (\<forall>x. G x) \<Longrightarrow> \<forall>x.(F x \<and> G x)"
        proof - 
          assume "(\<forall>x. F x) \<and> (\<forall>x. G x)"
          have "\<forall>x. F x" using \<open>(\<forall>x. F x) \<and> (\<forall>x. G x)\<close> by (rule conjunct1)
          have "\<forall>x. G x" using \<open>(\<forall>x. F x) \<and> (\<forall>x. G x)\<close> by (rule conjunct2)
          show "\<forall>x.(F x \<and> G x)"
          proof (rule allI)
            fix a
            have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
            have "G a" using \<open>\<forall>x. G x\<close> by (rule allE)
            show "F a \<and> G a" using \<open>F a\<close> \<open>G a\<close> by (rule conjI)
          qed
        qed

(*6.5.3.2*)
        have "\<forall>x.(F x \<and> G x) \<Longrightarrow> (\<forall>x. F x)\<and>(\<forall>x. G x)"
        proof - 
          assume "\<forall>x.(F x \<and> G x)"
          have "\<forall>x. F x"
          proof (rule allI)
            fix a
            have "F a \<and> G a" using \<open>\<forall>x.(F x \<and> G x)\<close> by (rule allE)
            show "F a" using \<open>F a \<and> G a\<close> by (rule conjunct1)
          qed
          have "\<forall>x. G x"
          proof (rule allI)
            fix a
            have "F a \<and> G a" using \<open>\<forall>x.(F x \<and> G x)\<close> by (rule allE)
            show "G a" using \<open>F a \<and> G a\<close> by (rule conjunct2)
          qed
          show "(\<forall>x. F x)\<and>(\<forall>x. G x)" 
            using \<open>\<forall>x. F x\<close> \<open>\<forall>x. G x\<close> by (rule conjI)
        qed

(*6.5.4*)
        have "(\<forall>x. F x) \<or> (\<forall>x. G x) \<Longrightarrow> \<forall>x.(F x \<or> G x)"
        proof - 
          assume "(\<forall>x. F x) \<or> (\<forall>x. G x)"
          show "\<forall>x.(F x \<or> G x)"
          proof (rule disjE[OF \<open>(\<forall>x. F x) \<or> (\<forall>x. G x)\<close>])
            assume "\<forall>x. F x"
            show "\<forall>x.(F x \<or> G x)"
            proof (rule allI)
              fix a
              have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
              show "F a \<or> G a" using \<open>F a\<close> by (rule disjI1)
            qed
          next
            assume "\<forall>x. G x"
            show "\<forall>x.(F x \<or> G x)"
            proof (rule allI)
              fix a
              have "G a" using \<open>\<forall>x. G x\<close> by (rule allE)
              show "F a \<or> G a" using \<open>G a\<close> by (rule disjI2)
            qed
          qed
        qed

(*6.5.5*)
        have "\<not> F a \<Longrightarrow> \<not>(\<forall>x. F x)"
        proof -
          fix a 
          assume "\<not> F a"
          have "(\<forall>x. F x) \<Longrightarrow> False"
          proof - 
            assume "\<forall>x. F x"
            have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
            show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
          qed
          show "\<not>(\<forall>x. F x)" 
            using \<open>\<forall>x. F x \<Longrightarrow> False\<close> by (rule notI) 
        qed

(*6.5.5.1*)
        have "\<not> F a \<Longrightarrow> \<not>(\<forall>x. F x)"
        proof -
          fix a 
          assume "\<not> F a"
          have "(\<forall>x. F x) \<longrightarrow> F a"
          proof (rule impI)
            assume "\<forall>x. F x"
            show "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
          qed
          show "\<not>(\<forall>x. F x)" 
            using \<open>(\<forall>x. F x) \<longrightarrow> F a\<close> \<open>\<not> F a\<close> by (rule mt)
        qed

(*6.5.6*)
        have "\<forall>x. \<not> F x \<Longrightarrow> \<forall>x. (F x \<longrightarrow> G x)"
        proof - 
          assume "\<forall>x. \<not> F x"
          show "\<forall>x. (F x \<longrightarrow> G x)"
          proof (rule allI)
            fix a 
            have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
            show "F a \<longrightarrow> G a" using \<open>\<not> F a\<close> by (rule NP)
          qed
        qed

(*6.5.7*)
        have "P \<Longrightarrow> \<forall>x.(F x \<longrightarrow> P)"
        proof - 
          assume "P"
          show "\<forall>x.(F x \<longrightarrow> P)"
          proof (rule allI)
            fix a
            show "F a \<longrightarrow> P"
            proof (rule impI)
              assume "F a"
              show "P" using \<open>P\<close> by assumption
            qed
          qed
        qed

(*6.5.7.1*)
        have "P \<Longrightarrow> \<forall>x.(F x \<longrightarrow> P)"
        proof - 
          assume "P"
          show "\<forall>x.(F x \<longrightarrow> P)"
          proof (rule allI)
            fix a
            show "F a \<longrightarrow> P" using \<open>P\<close> by (rule PP)
          qed
        qed

(*6.5.8.1*)
        have "P \<longrightarrow> (\<forall>x. F x) \<Longrightarrow> \<forall>x.(P \<longrightarrow> F x)"
        proof - 
          assume "P \<longrightarrow> (\<forall>x. F x)"
          show "\<forall>x.(P \<longrightarrow> F x)"
          proof (rule allI)
            fix a 
            show "P \<longrightarrow> F a"
            proof (rule impI)
              assume "P"
              have "\<forall>x. F x" 
                using \<open>P \<longrightarrow> (\<forall>x. F x)\<close> \<open>P\<close> by (rule mp)
              show "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
            qed
          qed
        qed

(*6.5.8.2*)
        have "\<forall>x.(P \<longrightarrow> F x) \<Longrightarrow> P \<longrightarrow> (\<forall>x. F x)"
        proof - 
          assume "\<forall>x.(P \<longrightarrow> F x)"
          show "P \<longrightarrow> (\<forall>x. F x)"
          proof (rule impI)
            assume "P"
            show "\<forall>x. F x" 
            proof (rule allI)
              fix a
              have "P \<longrightarrow> F a" using \<open>\<forall>x.(P \<longrightarrow> F x)\<close> by (rule allE)
              show "F a" using \<open>P \<longrightarrow> F a\<close> \<open>P\<close> by (rule mp)
            qed
          qed
        qed

(*6.5.9*)
        have "\<forall>x.(\<forall>y.(I x y)) \<Longrightarrow> \<forall>x.(I x x)"
        proof - 
          assume "\<forall>x.(\<forall>y.(I x y))"
          show "\<forall>x.(I x x)"
          proof (rule allI)
            fix a 
            have "\<forall>y.(I a y)" using \<open>\<forall>x.(\<forall>y.(I x y))\<close> by (rule allE)
            show "I a a" using \<open>\<forall>y.(I a y)\<close> by (rule allE)
          qed
        qed

(*6.5.10*)
        have "\<forall>x.(\<forall>y.(I x y)) \<Longrightarrow> \<forall>y.(\<forall>x.(I x y))"
        proof - 
          assume "\<forall>x.(\<forall>y.(I x y))"
          show "\<forall>y.(\<forall>x.(I x y))"
          proof (rule allI)
            fix b
            show "\<forall>x.(I x b)"
            proof (rule allI)
              fix a
              have "\<forall>y.(I a y)" using \<open>\<forall>x.(\<forall>y.(I x y))\<close> by (rule allE)
              show "I a b" using \<open>\<forall>y.(I a y)\<close> by (rule allE)
            qed
          qed
        qed
end

(*6.6.0.1*)
theorem not_ex_all_not: "\<not>(\<exists>x. F x) \<Longrightarrow> \<forall>x. \<not> F x"
        proof - 
          assume "\<not>(\<exists>x. F x)"
          show "\<forall>x. \<not> F x" 
          proof (rule allI)
            fix a
            have "F a \<Longrightarrow> False"
            proof - 
              assume "F a"
              have "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
              show "False" using \<open>\<not>(\<exists>x. F x)\<close> \<open>\<exists>x. F x\<close> by (rule notE)
            qed
            show "\<not> F a" using \<open>F a \<Longrightarrow> False\<close> by (rule notI)
          qed
        qed

notepad 
begin

(*6.6.0.2*)
        have "\<not>(\<exists>x.(\<not> F x)) \<Longrightarrow> \<forall>x.(F x)"
        proof - 
          assume "\<not>(\<exists>x.(\<not> F x))"
          show "\<forall>x.(F x)"
          proof (rule allI)
          fix a
          have "\<not> F a \<Longrightarrow> False"
          proof - 
            assume "\<not> F a"
            have "\<exists>x. \<not> F x" using \<open>\<not> F a\<close> by (rule exI)
            show "False" using \<open>\<not>(\<exists>x.(\<not> F x))\<close> \<open>\<exists>x. \<not> F x\<close> by (rule notE)
          qed
          have "\<not>\<not> F a" using \<open>\<not> F a \<Longrightarrow> False\<close> by (rule notI)
          show "F a" using \<open>\<not>\<not> F a\<close> by (rule notnotD)
        qed
      qed

(*6.6.1*)
      have "\<not>(\<exists>x.(F x \<and> G x)) \<Longrightarrow> \<forall>x.(F x \<longrightarrow> \<not> G x)"
      proof - 
        assume "\<not>(\<exists>x.(F x \<and> G x))"
        show "\<forall>x.(F x \<longrightarrow> \<not> G x)"
        proof (rule allI)
          fix a 
          show "F a \<longrightarrow> \<not> G a"
          proof (rule impI)
            assume "F a"
            have "G a \<Longrightarrow> False"
            proof - 
              assume "G a"
              have "F a \<and> G a" using \<open>F a\<close> \<open>G a\<close> by (rule conjI)
              have "\<exists>x.(F x \<and> G x)" using \<open>F a \<and> G a\<close> by (rule exI)
              show "False" 
                using \<open>\<not>(\<exists>x.(F x \<and> G x))\<close> \<open>\<exists>x.(F x \<and> G x)\<close> by (rule notE)
            qed
            show "\<not> G a" using \<open>G a \<Longrightarrow> False\<close> by (rule notI)
          qed
        qed
      qed

(*6.6.2*)
      have "\<forall>x. F x \<Longrightarrow> \<exists>x. F x"
      proof - 
        assume "\<forall>x. F x"
        have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
        show "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
      qed

(*6.6.3*)
      have "\<lbrakk>\<forall>x.(F x \<longrightarrow> G x); F a\<rbrakk> \<Longrightarrow> \<exists>x. G x"
      proof - 
        assume "\<forall>x.(F x \<longrightarrow> G x)"
        assume "F a"
        have "F a \<longrightarrow> G a" using \<open>\<forall>x.(F x \<longrightarrow> G x)\<close> by (rule allE)
        have "G a" using \<open>F a \<longrightarrow> G a\<close> \<open>F a\<close> by (rule mp)
        show "\<exists>x. G x" using \<open>G a\<close> by (rule exI)
      qed

(*6.6.4*)
      have "\<not> F a \<Longrightarrow> \<exists>x. F x \<longrightarrow> P"
      proof - 
        assume "\<not> F a"
        have "F a \<longrightarrow> P" using \<open>\<not> F a\<close> by (rule NP)
        show "\<exists>x. F x \<longrightarrow> P" using \<open>F a \<longrightarrow> P\<close> by (rule exI)
      qed

(*6.6.5*)
      have "\<not>(\<forall>x. F x) \<Longrightarrow> \<exists>x. (F x \<longrightarrow> P)"
      proof - 
        assume "\<not>(\<forall>x. F x)"
        have "\<not>(\<exists>x. (F x \<longrightarrow> P)) \<Longrightarrow> False" 
        proof - 
          assume "\<not>(\<exists>x. (F x \<longrightarrow> P))"
          have "\<forall>x. \<not>(F x \<longrightarrow> P)" 
            using \<open>\<not>(\<exists>x. (F x \<longrightarrow> P))\<close> by (rule not_ex_all_not)
          have "\<forall>x. F x"
          proof (rule allI)
            fix a
            have "\<not>(F a \<longrightarrow> P)" using \<open>\<forall>x. \<not>(F x \<longrightarrow> P)\<close> by (rule allE)
            have "F a \<and> \<not>P" using \<open>\<not>(F a \<longrightarrow> P)\<close> by (rule notimp_to_and)
            show "F a" using \<open>F a \<and> \<not>P\<close> by (rule conjunct1)
          qed
          show "False" using \<open>\<not>(\<forall>x. F x)\<close> \<open>\<forall>x. F x\<close> by (rule notE)
        qed
        have "\<not>\<not>(\<exists>x. (F x \<longrightarrow> P))" 
          using \<open>\<not>(\<exists>x. (F x \<longrightarrow> P)) \<Longrightarrow> False\<close> by (rule notI)
        show "\<exists>x. (F x \<longrightarrow> P)" using \<open>\<not>\<not>(\<exists>x. (F x \<longrightarrow> P))\<close> by (rule notnotD)
      qed

(*6.6.6*)
      have "\<not>(\<exists>x. F x) \<Longrightarrow> \<forall>x.(F x \<longrightarrow> G x)"
      proof - 
        assume "\<not>(\<exists>x. F x)"
        have "\<forall>x. \<not> F x" using \<open>\<not>(\<exists>x. F x)\<close> by (rule not_ex_all_not)
        show "\<forall>x.(F x \<longrightarrow> G x)"
        proof (rule allI)
          fix a
          have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
          show  "F a \<longrightarrow> G a" using \<open>\<not> F a\<close> by (rule NP)
        qed
      qed

(*6.6.7*)
      have "\<forall>x.(\<forall>y.(I x y)) \<Longrightarrow> \<exists>x. I x x"
      proof - 
        assume "\<forall>x.(\<forall>y.(I x y))" 
        have "\<forall>y.(I c y)" using \<open>\<forall>x.(\<forall>y.(I x y))\<close> by (rule allE)
        have "I c c" using \<open>\<forall>y.(I c y)\<close> by (rule allE)
        show "\<exists>x. I x x" using \<open>I c c\<close> by (rule exI)
      qed

(*6.6.8*)
      have "P \<longrightarrow> F a \<Longrightarrow> P \<longrightarrow> (\<exists>x. F x)"
      proof - 
        assume "P \<longrightarrow> F a"
        show "P \<longrightarrow> (\<exists>x. F x)"
        proof (rule impI)
          assume "P"
          have "F a" using \<open>P \<longrightarrow> F a\<close> \<open>P\<close> by (rule mp)
          show "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
        qed
      qed

(*6.6.9*)
      have "(\<exists>x. F x) \<longrightarrow> P \<Longrightarrow> \<forall>x. (F x \<longrightarrow> P)"
      proof - 
        assume "(\<exists>x. F x) \<longrightarrow> P" 
        show "\<forall>x. (F x \<longrightarrow> P)"
        proof (rule allI)
          fix a
          show "F a \<longrightarrow> P" 
          proof (rule impI)
            assume "F a"
            have "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
            show "P" using \<open>(\<exists>x. F x) \<longrightarrow> P\<close> \<open>\<exists>x. F x\<close> by (rule mp)
          qed
        qed
      qed

(*6.6.10*)
      have "\<not>(\<exists>x. F x) \<Longrightarrow> \<forall>x.(F x \<longrightarrow> P)"
      proof - 
        assume "\<not>(\<exists>x. F x)"
        have "\<forall>x. \<not> F x" using \<open>\<not>(\<exists>x. F x)\<close> by (rule not_ex_all_not)
        show "\<forall>x.(F x \<longrightarrow> P)"
        proof (rule allI)
          fix a 
          have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
          show "F a \<longrightarrow> P" using \<open>\<not> F a\<close> by (rule NP)
        qed
      qed

end
(*6.6.11.0*)
theorem all_not_imp: "\<forall>x. \<not> (F x \<longrightarrow> P) \<Longrightarrow> \<forall>x.(F x \<and> \<not> P)"
proof -
  assume "\<forall>x. \<not> (F x \<longrightarrow> P)"
  show "\<forall>x.(F x \<and> \<not> P)"
  proof (rule allI)
    fix a
    have "\<not> (F a \<longrightarrow> P)" using \<open>\<forall>x. \<not> (F x \<longrightarrow> P)\<close> by (rule allE)
    show "F a \<and> \<not> P" using \<open>\<not> (F a \<longrightarrow> P)\<close> by (rule notimp_to_and)
  qed
qed

theorem all_and_P: "\<forall>x.(F x \<and> P) \<Longrightarrow> (\<forall>x.(F x)) \<and> P"
proof - 
  assume "\<forall>x.(F x \<and> P)"
  have "\<forall>x.(F x)"
  proof (rule allI)
    fix a
    have "F a \<and> P" using \<open>\<forall>x.(F x \<and> P)\<close> by (rule allE)
    show "F a" using \<open>F a \<and> P\<close> by (rule conjunct1)
  qed
  have "F a \<and> P" using \<open>\<forall>x.(F x \<and> P)\<close> by (rule allE)
  have "P" using \<open>F a \<and> P\<close> by (rule conjunct2)
  show "(\<forall>x.(F x)) \<and> P" using \<open>\<forall>x.(F x)\<close> \<open>P\<close> by (rule conjI)
qed

notepad 
begin
(*6.6.11*) (*can be abbreviated*)
      have "\<not>(\<exists>x. F x \<longrightarrow> P) \<Longrightarrow> (\<forall>x. F x) \<and> \<not> P"
      proof - 
        assume "\<not>(\<exists>x. F x \<longrightarrow> P)"
        have "\<forall>x. \<not> (F x \<longrightarrow> P)" 
          using \<open>\<not>(\<exists>x. F x \<longrightarrow> P)\<close> by (rule not_ex_all_not)
        have "\<forall>x.(F x \<and> \<not> P)" 
          using \<open>\<forall>x. \<not> (F x \<longrightarrow> P)\<close> by (rule all_not_imp)
        show "(\<forall>x. F x) \<and> \<not> P" 
          using \<open>\<forall>x.(F x \<and> \<not> P)\<close> by (rule all_and_P)
      qed

end

theorem not_all_some_not: "\<not>(\<forall>x. F x) \<Longrightarrow> \<exists>x. \<not> F x"
proof - 
  assume "\<not>(\<forall>x. F x)"
  have "\<not>(\<exists>x. \<not> F x) \<longrightarrow> (\<forall>x. F x)"
  proof (rule impI)
    assume "\<not>(\<exists>x. \<not> F x)"
    have "\<forall>x. \<not>\<not> F x" using \<open>\<not>(\<exists>x. \<not> F x)\<close> by (rule not_ex_all_not)
    show "\<forall>x. F x"
    proof (rule allI)
      fix a
      have "\<not>\<not> F a" using \<open>\<forall>x. \<not>\<not> F x\<close> by (rule allE)
      show "F a" using \<open>\<not>\<not> F a\<close> by (rule notnotD)
    qed
  qed
  have "\<not>\<not>(\<exists>x. \<not> F x)" 
    using \<open>\<not>(\<exists>x. \<not> F x) \<longrightarrow> (\<forall>x. F x)\<close> \<open>\<not>(\<forall>x. F x)\<close> by (rule mt)
  show "\<exists>x. \<not> F x" using \<open>\<not>\<not>(\<exists>x. \<not> F x)\<close> by (rule notnotD)
qed

notepad 
begin


(*6.6.12*)
      have "(\<forall>x. F x) \<longrightarrow> P \<Longrightarrow> \<exists>x.(F x \<longrightarrow> P)"
      proof - 
        assume "(\<forall>x. F x) \<longrightarrow> P"
        have "\<not>(\<exists>x.(F x \<longrightarrow> P)) \<Longrightarrow> False"
        proof - 
          assume "\<not>(\<exists>x.(F x \<longrightarrow> P))"
          have "\<forall>x. \<not>(F x \<longrightarrow> P)" 
            using \<open>\<not>(\<exists>x.(F x \<longrightarrow> P))\<close> by (rule not_ex_all_not)
          have "\<forall>x.(F x \<and> \<not> P)" 
            using \<open>\<forall>x. \<not>(F x \<longrightarrow> P)\<close> by (rule all_not_imp)
          have "(\<forall>x.(F x)) \<and> \<not>P" 
            using \<open>\<forall>x.(F x \<and> \<not> P)\<close> by (rule all_and_P)
          have "\<not>((\<forall>x.(F x)) \<longrightarrow> P)" 
            using \<open>(\<forall>x.(F x)) \<and> \<not>P\<close> by (rule and_to_notimp)
          show "False" 
            using \<open>\<not>((\<forall>x.(F x)) \<longrightarrow> P)\<close> \<open>(\<forall>x. F x) \<longrightarrow> P\<close> by (rule notE)
        qed
        have "\<not>\<not>(\<exists>x.(F x \<longrightarrow> P))" 
          using \<open>\<not>(\<exists>x.(F x \<longrightarrow> P)) \<Longrightarrow> False\<close> by (rule notI)
        show "\<exists>x.(F x \<longrightarrow> P)" using \<open>\<not>\<not>(\<exists>x.(F x \<longrightarrow> P))\<close> by (rule notnotD)
      qed

(*6.7.1*)
      have "\<exists>x. F x \<and> G x \<Longrightarrow> \<exists>x. F x"
      proof - 
        assume "\<exists>x. F x \<and> G x"
        show "\<exists>x. F x"
        proof (rule exE[OF \<open>\<exists>x. F x \<and> G x\<close>])
        fix a 
        assume "F a \<and> G a"
        have "F a" using \<open>F a \<and> G a\<close> by (rule conjunct1)
        show "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
      qed
    qed

(*6.7.2*)
    have "\<lbrakk>\<forall>x. F x \<longrightarrow> G x; \<exists>x. F x\<rbrakk>  \<Longrightarrow> \<exists>x. G x"
    proof - 
      assume "\<forall>x. F x \<longrightarrow> G x"
      assume "\<exists>x. F x"
      show "\<exists>x. G x"
      proof (rule exE[OF \<open>\<exists>x. F x\<close>])
        fix a
        assume "F a"
        have "F a \<longrightarrow> G a" using \<open>\<forall>x. F x \<longrightarrow> G x\<close> by (rule allE)
        have "G a" using \<open>F a \<longrightarrow> G a\<close> \<open>F a\<close> by (rule mp)
        show "\<exists>x. G x" using \<open>G a\<close> by (rule exI)
      qed
    qed

(*6.7.3*)
    have "\<exists>x. F x \<or> G x \<Longrightarrow> (\<exists>x. F x)\<or>(\<exists>x. G x) "
    proof - 
      assume "\<exists>x. F x \<or> G x"
      show "(\<exists>x. F x)\<or>(\<exists>x. G x)"
      proof (rule exE[OF \<open>\<exists>x. F x \<or> G x\<close>])
        fix a
        assume "F a \<or> G a" 
        show "(\<exists>x. F x)\<or>(\<exists>x. G x)"
        proof (rule disjE[OF \<open>F a \<or> G a\<close>])
          assume "F a" 
          have "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
          show "(\<exists>x. F x)\<or>(\<exists>x. G x)" using \<open>\<exists>x. F x\<close> by (rule disjI1)
        next
          assume "G a"
          have "\<exists>x. G x" using \<open>G a\<close> by (rule exI)
          show "(\<exists>x. F x)\<or>(\<exists>x. G x)" using \<open>\<exists>x. G x\<close> by (rule disjI2)
        qed
      qed
    qed

(*6.7.4*)
    have "\<exists>x. \<not> F x \<Longrightarrow> \<not>(\<forall>x. F x)"
    proof - 
      assume "\<exists>x. \<not> F x"
      have "\<forall>x. F x \<Longrightarrow> False"
      proof - 
        assume "\<forall>x. F x"
        show "False"
        proof (rule exE [OF \<open>\<exists>x. \<not> F x\<close>])
          fix a
          assume "\<not> F a"
          have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
          show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
        qed
      qed
      show "\<not>(\<forall>x. F x)" using \<open>\<forall>x. F x \<Longrightarrow> False\<close> by (rule notI)
    qed

(*6.7.5*)
    have "\<exists>x. I x x \<Longrightarrow> \<exists>x.(\<exists>y. I x y)"
    proof - 
      assume "\<exists>x. I x x"
      show "\<exists>x.(\<exists>y. I x y)"
      proof (rule exE[OF \<open>\<exists>x. I x x\<close>])
        fix a 
        assume "I a a"
        have "\<exists>y. I a y" using \<open>I a a\<close> by (rule exI)
        show "\<exists>x.(\<exists>y. I x y)" using \<open>\<exists>y. I a y\<close> by (rule exI)
      qed
    qed

end
(*6.8.0.1*)
theorem all_notnot_all: "\<forall>x. \<not>\<not> F x \<Longrightarrow> \<forall>x. F x"
proof - 
  assume "\<forall>x. \<not>\<not> F x"
  show "\<forall>x. F x"
  proof (rule allI)
    fix a 
    have "\<not>\<not> F a" using \<open>\<forall>x. \<not>\<not> F x\<close> by (rule allE)
    show "F a" using \<open>\<not>\<not> F a\<close> by (rule notnotD)
  qed
qed

notepad
begin
(*6.8.1*)
    have "\<not>(\<forall>x. F x) \<Longrightarrow> \<exists>x. \<not> F x"
    proof - 
      assume "\<not>(\<forall>x. F x)"
      have "\<not>(\<exists>x. \<not> F x) \<Longrightarrow> False"
      proof -
        assume "\<not>(\<exists>x. \<not> F x)"
        have "\<forall>x. \<not>\<not> F x" using \<open>\<not>(\<exists>x. \<not> F x)\<close> by (rule not_ex_all_not)
        have "\<forall>x. F x" using \<open>\<forall>x. \<not>\<not> F x\<close> by (rule all_notnot_all)
        show "False" using \<open>\<not>(\<forall>x. F x)\<close> \<open>\<forall>x. F x\<close> by (rule notE)
      qed
      have "\<not>\<not>(\<exists>x. \<not> F x)" using \<open>\<not>(\<exists>x. \<not> F x) \<Longrightarrow> False\<close> by (rule notI)
      show "\<exists>x. \<not> F x" using \<open>\<not>\<not>(\<exists>x. \<not> F x)\<close> by (rule notnotD)
    qed

(*6.8.2*)
    have "\<forall>x. \<not> F x \<Longrightarrow> \<not>(\<exists>x. F x)"
    proof -
      assume "\<forall>x. \<not> F x"
      have "\<exists>x. F x \<Longrightarrow> False"
      proof - 
        assume "\<exists>x. F x"
        show "False"
        proof (rule exE[OF \<open>\<exists>x. F x\<close>])
          fix a
          assume "F a" 
          have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
          show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
        qed
      qed
      show "\<not>(\<exists>x. F x)" using \<open>\<exists>x. F x \<Longrightarrow> False\<close> by (rule notI)
    qed

end
(*6.8.3*)
    theorem some_not_not_all: "\<exists>x. \<not> F x \<Longrightarrow> \<not> (\<forall>x. F x)"
    proof - 
      assume "\<exists>x. \<not> F x"
      have "\<forall>x. F x \<Longrightarrow> False"
      proof - 
        assume "\<forall>x. F x"
        show "False"
        proof (rule exE[OF \<open>\<exists>x. \<not> F x\<close>])
          fix a
          assume "\<not> F a"
          have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
          show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
        qed
      qed
      show "\<not> (\<forall>x. F x)" using \<open>\<forall>x. F x \<Longrightarrow> False\<close> by (rule notI)
    qed

notepad 
begin
(*6.8.4*)
    have "\<not>(\<forall>x. \<not> F x) \<Longrightarrow> \<exists>x. F x"
    proof - 
      assume "\<not>(\<forall>x. \<not> F x)"
      have "\<not>(\<exists>x. F x) \<longrightarrow> (\<forall>x. \<not> F x)"
      proof (rule impI)
        assume "\<not>(\<exists>x. F x)"
        show "\<forall>x. \<not> F x" using \<open>\<not>(\<exists>x. F x)\<close> by (rule not_ex_all_not)
      qed
      have "\<not>\<not>(\<exists>x. F x)" 
        using \<open>\<not>(\<exists>x. F x) \<longrightarrow> (\<forall>x. \<not> F x)\<close> \<open>\<not>(\<forall>x. \<not> F x)\<close> by (rule mt)
      show "\<exists>x. F x" using \<open>\<not>\<not>(\<exists>x. F x)\<close> by (rule notnotD)
    qed

(*6.8.5*)
    have "\<exists>x. F x \<Longrightarrow> \<not>(\<forall>x. \<not> F x)"
    proof - 
      assume "\<exists>x. F x"
      have "\<forall>x. \<not> F x \<Longrightarrow> False"
      proof - 
        assume "\<forall>x. \<not> F x"
        show "False"
        proof (rule exE[OF \<open>\<exists>x. F x\<close>])
          fix a
          assume "F a"
          have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
          show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
        qed
      qed
      show "\<not>(\<forall>x. \<not> F x)" using \<open>\<forall>x. \<not> F x \<Longrightarrow> False\<close> by (rule notI)
    qed

(*6.11.1*)
    have "(\<exists>x. F x)\<or>(\<exists>x. G x) \<Longrightarrow> \<exists>x.(F x \<or> G x)"
    proof - 
      assume "(\<exists>x. F x)\<or>(\<exists>x. G x)"
      show "\<exists>x.(F x \<or> G x)"
      proof (rule disjE[OF \<open>(\<exists>x. F x)\<or>(\<exists>x. G x)\<close>])
        assume "\<exists>x. F x"
        show "\<exists>x.(F x \<or> G x)"
        proof (rule exE[OF \<open>\<exists>x. F x\<close>])
          fix a 
          assume "F a"
          have "F a \<or> G a" using \<open>F a\<close> by (rule disjI1)
          show "\<exists>x.(F x \<or> G x)" using \<open>F a \<or> G a\<close> by (rule exI)
        qed
      next
        assume "\<exists>x. G x"
        show "\<exists>x.(F x \<or> G x)"
        proof (rule exE[OF \<open>\<exists>x. G x\<close>])
          fix a 
          assume "G a"
          have "F a \<or> G a" using \<open>G a\<close> by (rule disjI2)
          show "\<exists>x.(F x \<or> G x)" using \<open>F a \<or> G a\<close> by (rule exI)
        qed
      qed
    qed

(*6.11.2*)
    have "\<lbrakk>\<forall>x.(F x \<longrightarrow> G x); \<not>(\<exists>x. G x)\<rbrakk> \<Longrightarrow> \<not>(\<exists>x. F x)"
    proof - 
      assume "\<forall>x.(F x \<longrightarrow> G x)"
      assume "\<not>(\<exists>x. G x)"
      have "\<forall>x. \<not> G x" using \<open>\<not>(\<exists>x. G x)\<close> by (rule not_ex_all_not)
      have "\<exists>x. F x \<Longrightarrow> False"
      proof - 
        assume "\<exists>x. F x"
        show "False"
        proof (rule exE[OF \<open>\<exists>x. F x\<close>])
        fix a 
        assume "F a"
        have "F a \<longrightarrow> G a" using \<open>\<forall>x.(F x \<longrightarrow> G x)\<close> by (rule allE)
        have "\<not> G a" using \<open>\<forall>x. \<not> G x\<close> by (rule allE) 
        have "\<not> F a" using \<open>F a \<longrightarrow> G a\<close> \<open>\<not> G a\<close> by (rule mt)
        show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
      qed
    qed
    show "\<not>(\<exists>x. F x)" using \<open>\<exists>x. F x \<Longrightarrow> False\<close> by (rule notI)
  qed

(*6.11.3*)
    have "\<forall>x. (F x \<longrightarrow> G x) \<Longrightarrow> (\<exists>x. \<not> G x) \<longrightarrow> (\<exists>x. \<not> F x)"
    proof - 
      assume "\<forall>x. (F x \<longrightarrow> G x)"
      show "(\<exists>x. \<not> G x) \<longrightarrow> (\<exists>x. \<not> F x)"
      proof (rule impI)
        assume "\<exists>x. \<not> G x"
        show "\<exists>x. \<not> F x"
        proof (rule exE[OF \<open>\<exists>x. \<not> G x\<close>])
          fix a
          assume "\<not> G a"
          have "F a \<longrightarrow> G a" using \<open>\<forall>x. (F x \<longrightarrow> G x)\<close> by (rule allE)
          have "\<not> F a" using \<open>F a \<longrightarrow> G a\<close> \<open>\<not> G a\<close> by (rule mt)
          show "\<exists>x. \<not> F x" using \<open>\<not> F a\<close> by (rule exI)
        qed
      qed
    qed

(*6.11.4*)
    have "\<forall>x. (F x \<longrightarrow> P) \<Longrightarrow> (\<exists>x. F x) \<longrightarrow> P"
    proof - 
      assume "\<forall>x. (F x \<longrightarrow> P)"
      show "(\<exists>x. F x) \<longrightarrow> P"
      proof (rule impI)
        assume "\<exists>x. F x"
        show "P" 
        proof (rule exE[OF \<open>\<exists>x. F x\<close>])
          fix a 
          assume "F a" 
          have "F a \<longrightarrow> P" using \<open>\<forall>x. (F x \<longrightarrow> P)\<close> by (rule allE)
          show "P" using \<open>F a \<longrightarrow> P\<close> \<open>F a\<close> by (rule mp)
        qed
      qed
    qed

(*6.11.5*)
    have "P \<and> (\<exists>x. F x) \<Longrightarrow> \<exists>x. (P \<and> F x)"
    proof - 
      assume "P \<and> (\<exists>x. F x)"
      have "P" using \<open>P \<and> (\<exists>x. F x)\<close> by (rule conjunct1)
      have "\<exists>x. F x" using \<open>P \<and> (\<exists>x. F x)\<close> by (rule conjunct2)
      show "\<exists>x. (P \<and> F x)"
      proof (rule exE[OF \<open>\<exists>x. F x\<close>])
        fix a 
        assume "F a"
        have "P \<and> F a" using \<open>P\<close> \<open>F a\<close> by (rule conjI)
        show "\<exists>x. (P \<and> F x)" using \<open>P \<and> F a\<close> by (rule exI)
      qed
    qed

(*6.11.6*)
    have "\<exists>x. (F x \<longrightarrow> P) \<Longrightarrow> (\<forall>x. F x) \<longrightarrow> P"
    proof - 
      assume "\<exists>x. (F x \<longrightarrow> P)"
      show "(\<forall>x. F x) \<longrightarrow> P"
      proof (rule impI)
        assume "\<forall>x. F x"
        show "P"
        proof (rule exE[OF \<open>\<exists>x. (F x \<longrightarrow> P)\<close>])
          fix a 
          assume "F a \<longrightarrow> P"
          have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
          show "P" using \<open>F a \<longrightarrow> P\<close> \<open>F a\<close> by (rule mp)
        qed
      qed
    qed

(*6.11.7*)
    have "\<exists>x. (P \<longrightarrow> F x) \<Longrightarrow> P \<longrightarrow> (\<exists>x. F x)"
    proof - 
      assume "\<exists>x. (P \<longrightarrow> F x)"
      show "P \<longrightarrow> (\<exists>x. F x)"
      proof (rule impI)
        assume "P"
        show "\<exists>x. F x"
        proof (rule exE[OF \<open>\<exists>x. (P \<longrightarrow> F x)\<close>])
          fix a 
          assume "P \<longrightarrow> F a"
          have "F a" using \<open>P \<longrightarrow> F a\<close> \<open>P\<close> by (rule mp)
          show "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
        qed
      qed
    qed

(*6.11.8*)
    have "\<exists>x.(\<forall>y. I x y) \<Longrightarrow> \<forall>y.(\<exists>x. I x y)"
    proof - 
      assume "\<exists>x.(\<forall>y. I x y)"
      show "\<forall>y.(\<exists>x. I x y)"
      proof (rule allI)
        fix b
        show "\<exists>x. I x b"
        proof (rule exE [OF \<open>\<exists>x.(\<forall>y. I x y)\<close>])
          fix a 
          assume "\<forall>y. I a y"
          have "I a b" using \<open>\<forall>y. I a y\<close> by (rule allE)
          show "\<exists>x. I x b" using \<open>I a b\<close> by (rule exI)
        qed
      qed
    qed

(*6.11.9*)
    have "\<exists>x.(\<forall>y. H x y) \<Longrightarrow>  \<exists>x. H x x"
    proof -
      assume "\<exists>x.(\<forall>y. H x y)"
      show "\<exists>x. H x x"
      proof (rule exE[OF \<open>\<exists>x.(\<forall>y. H x y)\<close>])
        fix a 
        assume "\<forall>y. H a y"
        have "H a a" using \<open>\<forall>y. H a y\<close> by (rule allE)
        show "\<exists>x. H x x" using \<open>H a a\<close> by (rule exI)
      qed
    qed

(*6.12.1*)
    have "\<forall>x.(F x \<or> P) \<Longrightarrow> (\<forall>x. F x) \<or> P"
    proof - 
      assume "\<forall>x.(F x \<or> P)"
      have "\<not>((\<forall>x. F x) \<or> P) \<Longrightarrow> False"   
      proof - 
        assume "\<not>((\<forall>x. F x) \<or> P)"
        have "\<not>(\<forall>x. F x) \<and> \<not>P" using \<open>\<not>((\<forall>x. F x) \<or> P)\<close> by (rule DM1)
        have "\<not>(\<forall>x. F x)" using \<open>\<not>(\<forall>x. F x) \<and> \<not>P\<close> by (rule conjunct1)
        have "\<exists>x. \<not> F x" using \<open>\<not>(\<forall>x. F x)\<close> by (rule not_all_some_not)
        have "\<not>P" using \<open>\<not>(\<forall>x. F x) \<and> \<not>P\<close> by (rule conjunct2)
        have "\<not>(\<forall>x. (F x \<or> P))" 
        proof (rule exE[OF \<open>\<exists>x. \<not> F x\<close>])
          fix a
          assume "\<not> F a"
          have "\<not> F a \<and> \<not> P" using \<open>\<not> F a\<close> \<open>\<not> P\<close> by (rule conjI)
          have "\<not>(F a \<or> P)" using \<open>\<not> F a \<and> \<not> P\<close> by (rule DM1_)
          have "\<exists>x. \<not>(F x \<or> P)" using \<open>\<not>(F a \<or> P)\<close> by (rule exI)
          show "\<not>(\<forall>x. (F x \<or> P))" using \<open>\<exists>x. \<not>(F x \<or> P)\<close> by (rule some_not_not_all)
        qed
        show "False" using \<open>\<not>(\<forall>x. (F x \<or> P))\<close> \<open>\<forall>x.(F x \<or> P)\<close> by (rule notE)
      qed
      have "\<not>\<not>((\<forall>x. F x) \<or> P)" using \<open>\<not>((\<forall>x. F x) \<or> P) \<Longrightarrow> False\<close> by (rule notI)
      show "(\<forall>x. F x) \<or> P" using \<open>\<not>\<not>((\<forall>x. F x) \<or> P)\<close> by (rule notnotD)
    qed

(*6.12.2*)
    have "(\<forall>x. F x) \<or> P \<Longrightarrow> \<forall>x.(F x \<or> P)"
    proof - 
      assume "(\<forall>x. F x) \<or> P"
      show "\<forall>x.(F x \<or> P)"
      proof (rule disjE[OF \<open>(\<forall>x. F x) \<or> P\<close>])
        assume "\<forall>x. F x"
        show "\<forall>x.(F x \<or> P)"
        proof (rule allI)
          fix a
          have "F a" using \<open>\<forall>x. F x\<close> by (rule allE)
          show "F a \<or> P" using \<open>F a\<close> by (rule disjI1)
        qed
      next
        assume "P"
        show "\<forall>x.(F x \<or> P)"
        proof (rule allI)
        fix a
        show "F a \<or> P" using \<open>P\<close> by (rule disjI2)
      qed
    qed
  qed

(*6.12.3*)
  have "\<exists>x.(F x \<or> P) \<Longrightarrow> (\<exists>x. F x) \<or> P"
  proof - 
    assume "\<exists>x.(F x \<or> P)"
    show "(\<exists>x. F x) \<or> P"
    proof (rule exE[OF \<open>\<exists>x.(F x \<or> P)\<close>])
      fix a
      assume "F a \<or> P"
      show "(\<exists>x. F x) \<or> P"
      proof (rule disjE[OF \<open>F a \<or> P\<close>])
        assume "F a"
        have "\<exists>x. F x" using \<open>F a\<close> by (rule exI)
        show "(\<exists>x. F x) \<or> P" using \<open>\<exists>x. F x\<close> by (rule disjI1)
      next
        assume "P"
        show "(\<exists>x. F x) \<or> P" using \<open>P\<close> by (rule disjI2)
      qed
    qed
  qed

(*6.12.4*)
  have "P \<longrightarrow> (\<exists>x. F x) \<Longrightarrow> \<exists>x.(P \<longrightarrow> F x)" 
  proof - 
    assume "P \<longrightarrow> (\<exists>x. F x)"
    have "\<not>P \<or> (\<exists>x. F x)" using \<open>P \<longrightarrow> (\<exists>x. F x)\<close> by (rule imp_to_or)
    show "\<exists>x.(P \<longrightarrow> F x)"
    proof (rule disjE[OF \<open>\<not>P \<or> (\<exists>x. F x)\<close>])
      assume "\<not>P"
      fix a
      have "P \<longrightarrow> F a" using \<open>\<not>P\<close> by (rule NP)
      show "\<exists>x.(P \<longrightarrow> F x)" using \<open>P \<longrightarrow> F a\<close> by (rule exI)
    next
      assume "\<exists>x. F x"
      show "\<exists>x.(P \<longrightarrow> F x)"
      proof (rule exE[OF \<open>\<exists>x. F x\<close>])
        fix b
        assume "F b"
        have "P \<longrightarrow> F b" using \<open>F b\<close> by (rule PP)
        show "\<exists>x.(P \<longrightarrow> F x)" using \<open>P \<longrightarrow> F b\<close> by (rule exI)
      qed
    qed
  qed

(*6.12.5*)
  have "\<exists>x.(\<exists>y. I x y) \<Longrightarrow> \<exists>y.(\<exists>x. I x y)"
  proof - 
    assume "\<exists>x.(\<exists>y. I x y)"
    show "\<exists>y.(\<exists>x. I x y)"
    proof (rule exE[OF \<open>\<exists>x.(\<exists>y. I x y)\<close>])
      fix a 
      assume "\<exists>y. I a y"
      show "\<exists>y.(\<exists>x. I x y)"
      proof (rule exE[OF \<open>\<exists>y. I a y\<close>])
        fix b
        assume "I a b"
        have "\<exists>x.(I x b)" using \<open>I a b\<close> by (rule exI)
        show "\<exists>y.(\<exists>x. I x y)" using \<open>\<exists>x.(I x b)\<close> by (rule exI) 
      qed
    qed
  qed

(*6.13.1*)

  have "\<forall>x.(F x \<or> \<not> F x)"
  proof - 
    have "\<not>(\<forall>x.(F x \<or> \<not> F x)) \<Longrightarrow> False"
    proof - 
      assume "\<not>(\<forall>x.(F x \<or> \<not> F x))"
      have "\<exists>x.\<not>(F x \<or> \<not> F x)" 
        using \<open>\<not>(\<forall>x.(F x \<or> \<not> F x))\<close> by (rule not_all_some_not)
      show "False"
      proof (rule exE[OF \<open>\<exists>x.\<not>(F x \<or> \<not> F x)\<close>])
        fix a
        assume "\<not>(F a \<or> \<not> F a)"
        have "\<not> F a \<and> \<not> \<not> F a" using \<open>\<not>(F a \<or> \<not> F a)\<close> by (rule DM1)
        have "\<not> F a" using \<open>\<not> F a \<and> \<not> \<not> F a\<close> by (rule conjunct1)
        have "\<not> \<not> F a" using \<open>\<not> F a \<and> \<not> \<not> F a\<close> by (rule conjunct2)
        show "False" using \<open>\<not> \<not> F a\<close> \<open>\<not> F a\<close> by (rule notE)
      qed
    qed
    have "\<not>\<not>(\<forall>x.(F x \<or> \<not> F x))" 
      using \<open>\<not>(\<forall>x.(F x \<or> \<not> F x)) \<Longrightarrow> False\<close> by (rule notI)
    show "\<forall>x.(F x \<or> \<not> F x)" using \<open>\<not>\<not>(\<forall>x.(F x \<or> \<not> F x))\<close> by (rule notnotD)
  qed  

(*6.13.2*)
  have "\<not>(\<exists>x.(\<forall>y.(\<not> R y y \<longleftrightarrow> R x y)))"
  proof - 
    have "\<exists>x.(\<forall>y.(\<not> R y y \<longleftrightarrow> R x y)) \<Longrightarrow> False"
    proof - 
      assume "\<exists>x.(\<forall>y.(\<not> R y y \<longleftrightarrow> R x y))"
      show "False" 
      proof (rule exE[OF \<open>\<exists>x.(\<forall>y.(\<not> R y y \<longleftrightarrow> R x y))\<close>])
        fix a 
        assume "\<forall>y.(\<not> R y y \<longleftrightarrow> R a y)"
        have "\<not> R a a \<longleftrightarrow> R a a" using \<open>\<forall>y.(\<not> R y y \<longleftrightarrow> R a y)\<close>
          by (rule allE)
        have "\<not> R a a \<Longrightarrow> R a a"
          using \<open>\<not> R a a \<longleftrightarrow> R a a\<close> by (rule iffD1)
        have "\<not> R a a \<longrightarrow> R a a" 
          using \<open>\<not> R a a \<Longrightarrow> R a a\<close> by (rule impI)
        have "R a a \<Longrightarrow> \<not> R a a"
          using \<open>\<not> R a a \<longleftrightarrow> R a a\<close> by (rule iffD2)
        have "R a a \<longrightarrow> \<not> R a a" 
          using \<open>R a a \<Longrightarrow> \<not> R a a\<close> by (rule impI)
        have "R a a \<or> \<not> R a a" by (rule lem)
        show "False"
        proof (rule disjE[OF \<open>R a a \<or> \<not> R a a\<close>])
          assume "R a a"
          have "\<not> R a a" using \<open>R a a \<longrightarrow> \<not> R a a\<close> \<open>R a a\<close> by (rule mp)
          show "False" using \<open>\<not> R a a\<close> \<open>R a a\<close> by (rule notE)
        next
          assume "\<not> R a a"
          have "R a a" using \<open>\<not> R a a \<longrightarrow> R a a\<close> \<open>\<not> R a a\<close> by (rule mp)
          show "False" using \<open>\<not> R a a\<close> \<open>R a a\<close> by (rule notE)
        qed
      qed
    qed
    show "\<not>(\<exists>x.(\<forall>y.(\<not> R y y \<longleftrightarrow> R x y)))"
      using \<open>\<exists>x.(\<forall>y.(\<not> R y y \<longleftrightarrow> R x y)) \<Longrightarrow> False\<close> by (rule notI)
  qed

(*6.14.1*)
  have "\<forall>x. (F x \<longrightarrow> F x)"
  proof - 
    show "\<forall>x. (F x \<longrightarrow> F x)"
    proof (rule allI)
      fix a 
      show "F a \<longrightarrow> F a"
      proof (rule impI)
        assume "F a"
        show "F a" using \<open>F a\<close> by assumption
      qed
    qed
  qed

(*6.14.2*)

  have "(\<forall>x. F x) \<or> (\<exists>x. \<not> F x)"
  proof - 
    have "\<not>((\<forall>x. F x) \<or> (\<exists>x. \<not> F x)) \<Longrightarrow> False"
    proof - 
      assume "\<not>((\<forall>x. F x) \<or> (\<exists>x. \<not> F x))"
      have "\<not>(\<forall>x. F x) \<and> \<not>(\<exists>x. \<not> F x)" 
        using \<open>\<not>((\<forall>x. F x) \<or> (\<exists>x. \<not> F x))\<close> by (rule DM1)
      have "\<not>(\<forall>x. F x)" 
        using \<open>\<not>(\<forall>x. F x) \<and> \<not>(\<exists>x. \<not> F x)\<close> by (rule conjunct1)
      have "\<not>(\<exists>x. \<not> F x)" 
        using \<open>\<not>(\<forall>x. F x) \<and> \<not>(\<exists>x. \<not> F x)\<close> by (rule conjunct2)
      have "\<exists>x. \<not> F x" using \<open>\<not>(\<forall>x. F x)\<close> by (rule not_all_some_not)
      have "\<forall>x. \<not>\<not> F x" using \<open>\<not>(\<exists>x. \<not> F x)\<close> by (rule not_ex_all_not)
      show "False"
      proof (rule exE[OF \<open>\<exists>x. \<not> F x\<close>])
        fix a 
        assume "\<not> F a"
        have "\<not>\<not> F a" using \<open>\<forall>x. \<not>\<not> F x\<close> by (rule allE)
        show "False" using \<open>\<not>\<not> F a\<close> \<open>\<not>F a\<close> by (rule notE)
      qed
    qed
    have "\<not>\<not>((\<forall>x. F x) \<or> (\<exists>x. \<not> F x))" 
      using \<open>\<not>((\<forall>x. F x) \<or> (\<exists>x. \<not> F x)) \<Longrightarrow> False\<close> by (rule notI)
    show "(\<forall>x. F x) \<or> (\<exists>x. \<not> F x)" 
      using \<open>\<not>\<not>((\<forall>x. F x) \<or> (\<exists>x. \<not> F x))\<close> by (rule notnotD)
  qed

(*6.14.3*)
  have "\<forall>x.\<not>(F x \<and> \<not> F x)"
  proof - 
    show "\<forall>x.\<not>(F x \<and> \<not> F x)"
    proof (rule allI)
      fix a 
      have "\<not> F a \<or> \<not>\<not> F a" by (rule lem)
      show "\<not>(F a \<and> \<not> F a)" using \<open>\<not> F a \<or> \<not>\<not> F a\<close> by (rule DM2_)
    qed
  qed

(*6.14.4*)
  have "\<not>(\<exists>x. F x \<and> \<not> F x)"
  proof - 
    have "\<exists>x. F x \<and> \<not> F x \<Longrightarrow> False"
    proof - 
      assume "\<exists>x. F x \<and> \<not> F x"
      show "False"
      proof (rule exE[OF \<open>\<exists>x. F x \<and> \<not> F x\<close>])
        fix a 
        assume "F a \<and> \<not> F a"
        have "F a" using \<open>F a \<and> \<not> F a\<close> by (rule conjunct1)
        have "\<not> F a" using \<open>F a \<and> \<not> F a\<close> by (rule conjunct2)
        show "False" using \<open>\<not> F a\<close> \<open>F a\<close> by (rule notE)
      qed
    qed
    show "\<not>(\<exists>x. F x \<and> \<not> F x)" using \<open>\<exists>x. F x \<and> \<not> F x \<Longrightarrow> False\<close> by (rule notI)
  qed

(*6.14.5*)
  have "\<forall>x. (\<exists>y. J x y \<longrightarrow> J x x)"
  proof - 
    show "\<forall>x. (\<exists>y. J x y \<longrightarrow> J x x)"
    proof (rule allI)
      fix a
      have "J a a \<longrightarrow> J a a"
      proof (rule impI)
        assume "J a a"
        show "J a a" using \<open>J a a\<close> by assumption
      qed
      show "\<exists>y. J a y \<longrightarrow> J a a" using \<open>J a a \<longrightarrow> J a a\<close> by (rule exI)
    qed
  qed

(*6.14.6*)
  have "\<forall>x. (\<exists>y. J x y \<longrightarrow> J y x)"
  proof - 
    show "\<forall>x. (\<exists>y. J x y \<longrightarrow> J y x)"
    proof (rule allI)
      fix a 
      have "J a a \<longrightarrow> J a a"
      proof (rule impI)
        assume "J a a"
        show "J a a" using \<open>J a a\<close> by assumption
      qed
      show "\<exists>y. J a y \<longrightarrow> J y a" using \<open>J a a \<longrightarrow> J a a\<close> by (rule exI)
    qed
  qed

(*6.14.7*)
  have "\<exists>x. F x \<longrightarrow> (\<forall>y. F y)"
  proof - 
    have "(\<forall>y. F y) \<or> \<not>(\<forall>y. F y)" by (rule lem)
    show "\<exists>x. F x \<longrightarrow> (\<forall>y. F y)" 
    proof (rule disjE[OF \<open>(\<forall>y. F y) \<or> \<not>(\<forall>y. F y)\<close>])
      assume "\<forall>y. F y"
      have "F a \<longrightarrow> (\<forall>y. F y)" using \<open>\<forall>y. F y\<close> by (rule PP)
      show "\<exists>x. F x \<longrightarrow> (\<forall>y. F y)" using \<open>F a \<longrightarrow> (\<forall>y. F y)\<close> by (rule exI)
    next
      assume "\<not>(\<forall>y. F y)"
      have "\<exists>y. \<not> F y" using \<open>\<not>(\<forall>y. F y)\<close> by (rule not_all_some_not)
      show "\<exists>x. F x \<longrightarrow> (\<forall>y. F y)"
      proof (rule exE[OF \<open>\<exists>y. \<not> F y\<close>])
        fix a 
        assume "\<not> F a"
        have "F a \<longrightarrow> (\<forall>y. F y)" using \<open>\<not> F a\<close> by (rule NP)
        show "\<exists>x. F x \<longrightarrow> (\<forall>y. F y)" using \<open>F a \<longrightarrow> (\<forall>y. F y)\<close> by (rule exI)
      qed
    qed
  qed

(*6.14.8*)
  have "\<exists>x. (\<forall>y. F x \<longrightarrow> F y)"
  proof - 
    have "(\<forall>z. F z) \<or> \<not>(\<forall>z. F z)" by (rule lem)
    show "\<exists>x. (\<forall>y. F x \<longrightarrow> F y)"
    proof (rule disjE [OF \<open>(\<forall>z. F z) \<or> \<not>(\<forall>z. F z)\<close>])
      assume "\<forall>z. F z"
      fix a 
      have "\<forall>y. F a \<longrightarrow> F y" 
      proof (rule allI)
        fix b 
        have "F b" using \<open>\<forall>z. F z\<close> by (rule allE)
        show "F a \<longrightarrow> F b"
        proof (rule impI)
          assume "F a" 
          show "F b" using \<open>F b\<close> by assumption
        qed
      qed
      show "\<exists>x. (\<forall>y. F x \<longrightarrow> F y)" using \<open>\<forall>y. F a \<longrightarrow> F y\<close> by (rule exI)
    next
      assume "\<not>(\<forall>z. F z)"
      have "\<exists>z. \<not> F z" using \<open>\<not>(\<forall>z. F z)\<close> by (rule not_all_some_not)
      show "\<exists>x. (\<forall>y. F x \<longrightarrow> F y)"
      proof (rule exE[OF \<open>\<exists>z. \<not> F z\<close>])
        fix a
        assume "\<not> F a"
        have "\<forall>y. F a \<longrightarrow> F y"
        proof (rule allI)
          fix b
          show "F a \<longrightarrow> F b" using \<open>\<not> F a\<close> by (rule NP)
        qed
        show "\<exists>x. (\<forall>y. F x \<longrightarrow> F y)" using \<open>\<forall>y. F a \<longrightarrow> F y\<close> by (rule exI)
      qed
    qed
  qed

(*6.14.9*)
  have "\<forall>x. (\<exists>y. F x \<longrightarrow> G y) \<Longrightarrow> \<exists>y. (\<forall>x. F x \<longrightarrow> G y)"
  proof - 
    assume "\<forall>x. (\<exists>y. F x \<longrightarrow> G y)"
    have "(\<exists>y. G y) \<or> \<not>(\<exists>y. G y)" by (rule lem)
    show "\<exists>y. (\<forall>x. F x \<longrightarrow> G y)"
    proof (rule disjE[OF \<open>(\<exists>y. G y) \<or> \<not>(\<exists>y. G y)\<close>])
      assume "\<exists>y. G y"
      show "\<exists>y. (\<forall>x. F x \<longrightarrow> G y)"
      proof (rule exE[OF \<open>\<exists>y. G y\<close>])
        fix b
        assume "G b"
        have "\<forall>x. F x \<longrightarrow> G b"
        proof (rule allI)
          fix a
          show "F a \<longrightarrow> G b"
          proof (rule impI)
            assume "F a"
            show "G b" using \<open>G b\<close> by assumption
          qed
        qed
        show "\<exists>y. (\<forall>x. F x \<longrightarrow> G y)" using \<open>\<forall>x. F x \<longrightarrow> G b\<close> by (rule exI)
      qed
    next
      assume "\<not>(\<exists>y. G y)"
      have "\<forall>y. \<not> G y" using \<open>\<not>(\<exists>y. G y)\<close> by (rule not_ex_all_not)
      have "\<forall>x. \<not> F x" 
      proof (rule allI)
        fix a
        have "\<exists>y. F a \<longrightarrow> G y" using \<open>\<forall>x. (\<exists>y. F x \<longrightarrow> G y)\<close> by (rule allE)
        show "\<not> F a"
        proof (rule exE[OF \<open>\<exists>y. F a \<longrightarrow> G y\<close>])
          fix b
          assume "F a \<longrightarrow> G b"
          have "\<not> G b" using \<open>\<forall>y. \<not> G y\<close> by (rule allE)
          show "\<not> F a" using \<open>F a \<longrightarrow> G b\<close> \<open>\<not> G b\<close> by (rule mt)
        qed
      qed
      have "\<forall>x. F x \<longrightarrow> G b"
      proof (rule allI)
        fix a
        have "\<not> F a" using \<open>\<forall>x. \<not> F x\<close> by (rule allE)
        show "F a \<longrightarrow> G b" using \<open>\<not> F a\<close> by (rule NP)
      qed
      show "\<exists>y. (\<forall>x. F x \<longrightarrow> G y)" using \<open>\<forall>x. F x \<longrightarrow> G b\<close> by (rule exI)
    qed
  qed

(*6.14.10*)
  have "\<forall>x. (\<exists>y. I x y \<longrightarrow> (\<forall>z. I x z))"
  proof -
    have "(\<forall>z. I a z) \<or> \<not>(\<forall>z. I a z)" by (rule lem)
    show "\<forall>x. (\<exists>y. I x y \<longrightarrow> (\<forall>z. I x z))"
    proof (rule disjE [OF \<open>(\<forall>z. I a z) \<or> \<not>(\<forall>z. I a z)\<close>])
      assume "\<forall>z. I a z"


















end