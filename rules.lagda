\begin{figure}
\[
\def\arraystretch{1.3}
\begin{array}{l l l}
⟦ c ⟧_ρ &= c & c ∈ \{⊤,⊥\}\\
⟦ A ∙ B ⟧_ρ &= ⟦ A ⟧_ρ ∙ ⟦ B ⟧_ρ & ∙ ∈ \{×,+,→\}\\
⟦ ∀ κ. A ⟧_ρ &= ∀ i.\, ⟦ A ⟧_{(ρ, κ ↦ i)}\\
⟦ ∃ κ. A ⟧_ρ &= ∃ i.\, ⟦ A ⟧_{(ρ, κ ↦ i)}\\
⟦ \trit^\kappa A ⟧_ρ &= ∀ j < ρ(\kappa).\, ⟦ A ⟧_{(ρ, κ ↦ j)}\\
⟦ \trib^\kappa A ⟧_ρ &= ∃ j < ρ(\kappa).\, ⟦ A ⟧_{(ρ, κ ↦ j)}\\
\end{array}
\]
\caption{Interpretation of modalities into |Time| quantification}
\label{fig:translation}
\end{figure}


\begin{figure}
\begin{mathpar}
\inferrule{Γ \vdash A :\Type \\ Γ ,\, x : A \vdash B :\Type}{Γ \vdash (x : A) \to B :\Type}
\and \inferrule{Γ \vdash A :\Type \\ Γ ,\, x : A \vdash B :\Type}{Γ \vdash Σ (x : A).\, B :\Type}
\and \inferrule{Γ \vdash A :\Type \\ Γ \vdash B :\Type}{Γ \vdash A + B :\Type}
\and \inferrule{Γ \vdash A :\Type \\ Γ \vdash B :\Type}{Γ \vdash A × B :\Type}
\and \inferrule{Γ \vdash \\ X = ⊥ , ⊤ , \Bool}{Γ \vdash X :\Type}

%% Universe
\and \inferrule{Γ \vdash}{Γ \vdash \U :\Type}
\and \inferrule{Γ \vdash u : \U}{Γ \vdash \El~u :\Type}
%%\mytodo{add terms? e.g. lambda/case/constructor/..}
\end{mathpar}
\caption{Dependent Type Theory with a Universe}
\label{fig:TT}
\end{figure}

\begin{figure}
\begin{mathpar}
%% Time
\inferrule{ }{Γ \vdash \Time :\Type}
\and \inferrule{ }{Γ \vdash 0 : \Time}
\and \inferrule{Γ \vdash t : \Time}{Γ \vdash\, ↑ t : \Time}
\and \inferrule{Γ \vdash t_0 : \Time \\ Γ \vdash t_1 : \Time}
               {Γ \vdash t_0 ⊔ t_1 : \Time}
\and \inferrule{Γ \vdash t_0 : \Time \\ Γ \vdash t_1 : \Time}
               {Γ \vdash t_0 \leq t_1 :\Type}
\end{mathpar}
\caption{The \Time{} type}
\label{fig:Time}
\end{figure}


\begin{figure}
\begin{mathpar}
%% Fix
\inferrule{\Gamma ,\,i : \Time \vdash A[i] : \Type \\
           \Gamma \vdash f : \forall i .~(\forall j < i .~A[j]) \to A[i]}
               {\Gamma \vdash \mathsf{fix}~f: \forall i . A[i]}
\and \inferrule{f~i~(\mathsf{guard}_\flater~u~i) = u~i}{u~i = \tfix~f~i}
\end{mathpar}
where
\[
\begin{array}{l}
\mathsf{guard}_\flater : (∀ i.~A[i]) \to ∀ i.~∀ j < i.~A[j]\\
\mathsf{guard}_\flater~f = λ i~j .~ f~j
\end{array}
\]
\caption{Guarded Fixpoint}
\label{fig:fix}
\end{figure}

\begin{figure}
\begin{mathpar}
%% Codes
\inferrule{Γ , i : \Time \vdash A : U}{Γ \vdash ∀ i.\, A : U}
\and \inferrule{Γ , i : \Time \vdash A : U}{Γ \vdash ∃ i.\, A : U}
\and \inferrule{Γ \vdash t_0 : \Time \\ Γ \vdash t_1 : \Time}
               {Γ \vdash t_0 \leq t_1 : U}
\and \inferrule{Γ \vdash A : U \\ Γ , x : A \vdash B : U}{Γ \vdash (x : A) \to B : U}
\and \inferrule{Γ \vdash A : U \\ Γ , x : A \vdash B : U}{Γ \vdash Σ (x : A).~B : U}
\and \inferrule{Γ \vdash A : U \\ Γ \vdash B : U}{Γ \vdash A + B : U}
\and \inferrule{Γ \vdash A : U \\ Γ \vdash B : U}{Γ \vdash A × B : U}
\and \inferrule{Γ \vdash \\  X = ⊥ , ⊤ , \Bool }{Γ \vdash X : U}

%%\mytodo{maybe too boring to repeat all this for U? in the end it only lacks a code for \Time and doesn't contain an universe itself}
\end{mathpar}
\caption{Codes for the Universe U}
\label{fig:codes}
\end{figure}

%include exists.lagda
\begin{figure*}
\begin{mathpar}
  \inferrule{\Gamma\vdash t : \Time}
            {\Gamma \vdash \mathsf{refl}~t : t \leq t}
  \and
    \inferrule{\Gamma\vdash p_0 : t_0 \leq t_1 \\ \Gamma\vdash p_1 : t_1 \leq t_2}{\Gamma \vdash \mathsf{trans}~p_0~p_1 : t_0 \leq t_1}
  \and
  \inferrule{\Gamma\vdash t : \Time}
            {\Gamma \vdash \mathsf{zero}~t : 0 \leq t}
  \and
  \inferrule{\Gamma\vdash t : \Time}
            {\Gamma \vdash \mathsf{step}~t : t \leq~↑ t}\\
  \and
  \inferrule{\Gamma\vdash t_0 : \Time \\ \Gamma\vdash t_1 : \Time}
            {\Gamma\vdash \mathsf{⊔_0}~t_0~t_1 : t_0 \leq t_0 ⊔ t_1}
  \and
  \inferrule{\Gamma\vdash t_0 : \Time \\ \Gamma\vdash t_1 : \Time}
            {\Gamma\vdash \mathsf{⊔_1}~t_0~t_1 : t_1 \leq t_0 ⊔ t_1}
\end{mathpar}
\caption{\Time{} inequalities}
\label{fig:leq}
\end{figure*}

\begin{figure*}

\begin{align*}
∀ i .~\El~A &≅ \El~A & i ∉ \mathsf{fv}(A) \\
∀ i .~\El~(A[i]) &≅ ∀ i.~∀ j < i.~\El~(A[j]) & \mbox{witnessed by } (|guardt| , |forcet|) \\
(∀ i.~A) + (∀ i.~B) &≅ ∀ i.~(A + B) \\
∀ i.~Σ (x : \El~A).~B &≅ Σ (x : \El~A).~∀ i .~B & i ∉ \mathsf{fv}(A)\\
\\
∃ i .~\El~A &≅ \El~A & i ∉ \mathsf{fv}(A) \\
∃ i .~A[i] &≅ ∃ i.~∃ j < i.~A[j] & \mbox{witnessed by } (|guardb| , |forceb|) \\
(∃ i.~A) + (∃ i.~B) &≅ ∃ i.~(A + B)\\
(∃ i.~A[i]) × (∃ i.~B[i]) &≅ ∃ i.~(∃ j < i .~A[j] × ∃ j < i.~B[j])\\
Σ (x : \El~A).~∃ i.~B &≅ ∃ i.~Σ (x : \El~A).~B & i ∉ \mathsf{fv}(A)\\
∃ i .~(x : \El~A) \to ∃ j < i.~B[j] &≅ (x : \El~A) \to ∃ i .~B[i] & \mbox{finite } \El~A, i ∉ \mathsf{fv}(A) \\
∃ i .~∃ j .~A &≅ ∃ j .~∃ i .~A
\end{align*}



\caption{Type Isomorphisms}
\label{fig:isos}
\end{figure*}
