\begin{figure}
\begin{mathpar}
\inferrule{|Γ ⊢ A : Type| \\ |Γ , x : A ⊢ B : Type|}{|Γ ⊢ (x : A) -> B : Type|}
\and \inferrule{|Γ ⊢ A : Type| \\ |Γ , x : A ⊢ B : Type|}{|Γ ⊢ Σ (x : A). B : Type|}
\and \inferrule{|Γ ⊢ A : Type| \\ |Γ ⊢ B : Type|}{|Γ ⊢ A + B : Type|}
\and \inferrule{|Γ ⊢ A : Type| \\ |Γ ⊢ B : Type|}{|Γ ⊢ A × B : Type|}
\and \inferrule{|X = ⊥ , ⊤ , Bool|}{|Γ ⊢ X : Type|}

%% Universe
\and \inferrule{ }{|Γ ⊢ U : Type|}
\and \inferrule{|Γ ⊢ u : U|}{|Γ ⊢ El u : Type|}
%%\mytodo{add terms? e.g. lambda/case/constructor/..}
\end{mathpar}
\caption{Dependent Type Theory with a Universe Γ ⊢ A : Type}
\label{fig:TT}
\end{figure}

\begin{figure}
\begin{mathpar}
%% Time
\inferrule{ }{|Γ ⊢ Time : Type|}
\and \inferrule{ }{|Γ ⊢ 0 : Time|}
\and \inferrule{|Γ ⊢ t : Time|}{|Γ ⊢ ↑ t : Time|}
\and \inferrule{|Γ ⊢ t_0 : Time| \\ |Γ ⊢ t_0 : Time|}
               {|Γ ⊢ t_0 <= t_1|}
\end{mathpar}
\caption{The |Time| type}
\label{fig:Time}
\end{figure}

%include exists.lagda

\begin{figure}
\begin{mathpar}
%% Fix
\inferrule{|Γ , i : Time ⊢ A(i) : Type| \\
                |Γ ⊢ f : ∀ i . (∀ j : < i . A(j)) -> A(i)|}
               {|fix f : ∀ i . A(i)|}
\and \inferrule{|f i (guardt u i) = u i|}{|u = fix f|}
\and \inferrule{ }{|guardt f = λ i j -> f j|}

\end{mathpar}
\caption{Guarded Fixpoint combinator}
\label{fig:fix}
\end{figure}

\begin{figure}
\begin{mathpar}
%% Codes
\inferrule{|Γ , i : Time ⊢ A : U|}{|Γ ⊢ ∀ i . A : U|}
\and \inferrule{|Γ , i : Time ⊢ A : U|}{|Γ ⊢ ∃ i . A : U|}
\and \inferrule{|Γ ⊢ t_0 : Time| \\ |Γ ⊢ t_0 : Time|}
               {|Γ ⊢ t_0 <= t_1 : U|}
\and \inferrule{|Γ ⊢ A : U| \\ |Γ , x : A ⊢ B : U|}{|Γ ⊢ (x : A) -> B : U|}
\and \inferrule{|Γ ⊢ A : U| \\ |Γ , x : A ⊢ B : U|}{|Γ ⊢ Σ (x : A). B : U|}
\and \inferrule{|Γ ⊢ A : U| \\ |Γ ⊢ B : U|}{|Γ ⊢ A + B : U|}
\and \inferrule{|Γ ⊢ A : U| \\ |Γ ⊢ B : U|}{|Γ ⊢ A × B : U|}
\and \inferrule{| X = ⊥ , ⊤ , Bool |}{|Γ ⊢ X : U|}

%%\mytodo{maybe too boring to repeat all this for U? in the end it only lacks a code for |Time| and doesn't contain an universe itself}
\end{mathpar}
\caption{Codes for the Universe |U|}
\label{fig:codes}
\end{figure}

\begin{figure}
\begin{tabular}{c l}
|∀ i . El A ≅ El A| & |i ∉ fv(A)| \\
|(∀ i. A) + (∀ i. A) ≅ ∀ i. (A + B)| \\
|∀ i . El (A(i)) ≅ ∀ i. ∀ (j : < i). El (A(j))| & (|guardt| , |forcet|) \\
|∀ i. Σ (x : El A). B ≅ Σ (x : El A). ∀ i . B| & |i ∉ A|\\
\end{tabular}

\begin{tabular}{c l}
|∃ i . El A ≅ El A| & |i ∉ fv(A)| \\
|(∃ i. A) + (∃ i. B) ≅ ∃ i. (A + B)|\\
|(∃ i. A(i)) × (∃ i. B(i)) ≅ ∃ i. (∃ (j : < i) . A(j) × ∃ (j : < i). B(j))|\\
|∃ i . A(i) ≅ ∃ i. ∃ (j : < i). A(j)| & (|guardb| , |forceb|)\\
|Σ (x : El A). ∃ i. B ≅ ∃ i. Σ (x : El A). B| & (i ∉ fv(A))\\
|∃ i . (x : El A) -> B ≅ (x : El A) → ∃ i . B| & finite |El A|, (i ∉ fv(A)) \\
|∃ i . ∃ j . A ≅ ∃ j . ∃ i . A| \\
\end{tabular}
\caption{Type Isomorphisms}
\label{fig:isos}
\end{figure}
