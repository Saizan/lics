\begin{figure*}
\begin{mathpar}
%% Existential
\inferrule{|Γ , i : Time ⊢ A(i) : Type | \\ |Γ ⊢ t : Time|
                 \\ | Γ ⊢ e : A(t)|}
                {|Γ ⊢ (pack t e) : ∃ i . A(i)|}
\and \inferrule{|Γ , x : ∃ i . A ⊢ P(x) : U| \\ |Γ ⊢ e0 : ∃ i . A| \\ |Γ , i : Time , a : A ⊢ e1 : El (P (pack i a))|}
               {|Γ ⊢ case e0 of (pack i a) -> e1 : El (P(e0))|}

\and \inferrule[∃-β]{|Γ , x : ∃ i . A(i) ⊢ P(x) : U| \\ |Γ ⊢ t : Time| \\ |Γ ⊢ e0 : A(t)| \\ |Γ , i : Time , a : A(i) ⊢ e1(i,a) : El (P (pack i a))|}
               {|Γ ⊢ (case (pack t e0) of (pack i a) -> e1(i,a)) = e(t,e0) : El (P(pack t e0))|}

\and \inferrule[∃-η]{|Γ , x : ∃ i . A ⊢ P(x) : U| \\ |Γ , x : ∃ i . A, p : El (P(x)) ⊢ Q(x,p) : U| \\
                |Γ , i : Time , a : A ⊢ e1 : El (P (pack i a))| \\ |Γ ⊢ e0 : ∃ i . A| \\ |Γ , x : ∃ i . A, p : El (P(x)) ⊢ e2(x,p) : El (Q(x,p))| }
               {|Γ ⊢ e2(e0,case e0 of (pack i a) -> e1) = case e0 of (pack i a) -> e2((pack i a),e1) : Q(e0,case e0 of (pack i a) -> e1)|}
\end{mathpar}
\caption{Existential Time Quantifier}
\label{fig:exists}
\end{figure*}
