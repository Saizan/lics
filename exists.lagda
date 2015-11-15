\begin{figure*}
\begin{mathpar}
%% Existential
\inferrule{Γ ,\, i : \Time \vdash A : \Type}{Γ \vdash ∃ i .~A : \Type}
\and \inferrule{Γ ,\, i : \Time \vdash A[i] : \Type  \\ Γ \vdash t : \Time
                 \\  Γ \vdash e : A[t]}
                {Γ \vdash (t, e) : ∃ i .~A[i]}
\and \inferrule{Γ ,\, x : ∃ i .~A \vdash P[x] : \U \\
                Γ \vdash e_∃ : ∃ i .~A \\ Γ ,\,i : \Time ,\,a : A \vdash e_p : \El~(P [(i, a)])}
               {Γ \vdash \case~e_∃~\tof~(i, a)~\to~e_p : \El~(P[e_∃])}

\and \inferrule[∃-β]{Γ ,\,x : ∃ i .~A[i] \vdash P[x] : \U \\ Γ \vdash t : \Time \\ Γ \vdash e_a : A[t] \\ Γ ,\,i : \Time ,\,x : A[i] \vdash e_p[i,x] :
     \El~(P[(i, x)])}
               {Γ \vdash (\case~(t, e_a)~\tof~(i, x)~\to~e_p[i,x]) = e_p[t, e_a] : \El~(P[(t, e_a)])}

\and \inferrule[∃-η]{Γ ,\,x : ∃ i .~A \vdash P[x] : \U \\ Γ ,\,x : ∃ i .~A,\,p : \El~(P[x]) \vdash Q[x,p] : \U \\
                Γ ,\,i : \Time ,\,a : A \vdash e_p : \El~(P[(i, a)])
                \\ Γ \vdash e_∃ : ∃ i .~A
                \\ Γ ,\,x : ∃ i .~A,\,p : \El~(P[x]) \vdash e_q[x,p] : \El~(Q[x,p]) }
               {Γ \vdash e_q[e_∃,\case~e_∃~\tof (i, a) \to e_p] = \case~e_∃~\tof~(i, a)~\to e_q[(i, a),e_p] : Q[e_∃,\case~e_∃~\tof~(i, a)~\to~e_p]}
\end{mathpar}
\caption{Existential \Time{} Quantifier}
\label{fig:exists}
\end{figure*}
