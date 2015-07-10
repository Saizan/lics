\begin{figure*}
\begin{mathpar}
%% Existential
\inferrule{Γ ,\, i : \Time \vdash A : \Type}{Γ \vdash ∃ i .~A : \Type}
\and \inferrule{Γ ,\, i : \Time \vdash A[i] : \Type  \\ Γ \vdash t : \Time
                 \\  Γ \vdash e : A[t]}
                {Γ \vdash (t, e) : ∃ i .~A[i]}
\and \inferrule{Γ ,\, x : ∃ i .~A \vdash P[x] : \U \\
                Γ \vdash e_0 : ∃ i .~A \\ Γ ,\,i : \Time ,\,a : A \vdash e_1 : \El~(P [(i, a)])}
               {Γ \vdash \case~e_0~\tof~(i, a)~\to~e_1 : \El~(P[e_0])}

\and \inferrule[∃-β]{Γ ,\,x : ∃ i .~A[i] \vdash P[x] : \U \\ Γ \vdash t : \Time \\ Γ \vdash e_0 : A[t] \\ Γ ,\,i : \Time ,\,a : A[i] \vdash e_1[i,a] :
     \El~(P[(i, a)])}
               {Γ \vdash (\case~(t, e_0)~\tof~(i, a)~\to~e_1[i,a]) = e_1[t,e_0] : \El~(P[(t, e_0)])}

\and \inferrule[∃-η]{Γ ,\,x : ∃ i .~A \vdash P[x] : \U \\ Γ ,\,x : ∃ i .~A,\,p : \El~(P[x]) \vdash Q[x,p] : \U \\
                Γ ,\,i : \Time ,\,a : A \vdash e_1 : \El~(P[(i, a)])
                \\ Γ \vdash e_0 : ∃ i .~A \\ Γ ,\,x : ∃ i .~A,\,p : \El~(P[x]) \vdash e_2[x,p] : \El~(Q[x,p]) }
               {Γ \vdash e_2[e_0,\case~e_0~\tof (i, a) \to e_1] = \case~e_0~\tof~(i, a)~\to e_2[(i, a),e_1] : Q[e_0,\case~e_0~\tof~(i, a)~\to~e_1]}
\end{mathpar}
\caption{Existential \Time{} Quantifier}
\label{fig:exists}
\end{figure*}
