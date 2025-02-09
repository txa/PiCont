\documentclass{easychair}
%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt
\usepackage{amssymb}

% use this if you have a long article and want to create an index
% \usepackage{makeidx}

% In order to save space or manage large tables or figures in a
% landcape-like text, you can use the rotating and pdflscape
% packages. Uncomment the desired from the below.
%
% \usepackage{rotating}
% \usepackage{pdflscape}

% Some of our commands for this guide.
%

%\makeindex

%% Front Matter
%%
% Regular title as in the article class.
%
\title{$\Pi$-types for the container model}

% Authors are joined by \and. Their affiliations are given by \inst, which indexes
% into the list defined using \institute
%
\author{
  Thorsten Altenkirch\inst{1} \and
  Stefania Damato\inst{1} \and
  Ambrus Kaposi\inst{2}
}

\institute{
  School of Computer Science, University of Nottingham, UK\\
  \email{\{psztxa,psxsd7\}@@nottingham.ac.uk}
  \and
  Department of Computer Science, Eötvös Loránd University
  (ELTE), Hungary \\
  \email{akaposi@@inf.elte.hu}  
}


% \institute{
%   \inst{1} School of Computer Science, University of Nottingham, UK\\
%   \email{\{psztxa,psxsd7\}@@nottingham.ac.uk}
%   \and
%   \inst{2} Department of Computer Science, Eötvös Loránd University
%   (ELTE), Hungary \\
%   \email{akaposi@@inf.elte.hu}  
% }


%  \authorrunning{} has to be set for the shorter version of the authors' names;
% otherwise a warning will be rendered in the running heads. When processed by
% EasyChair, this command is mandatory: a document without \authorrunning
% will be rejected by EasyChair

\authorrunning{Altenkirch, Damato,Kaposi}

% \titlerunning{} has to be set to either the main title or its shorter
% version for the running heads. When processed by
% EasyChair, this command is mandatory: a document without \titlerunning
% will be rejected by EasyChair
\titlerunning{Quotient inductive types as categorified containers}

\begin{document}

\maketitle

Strictly positive types can be represented as containers, that is 
|S : Set| and a family of positions |P : S → Set| giving rise to a
functor |S ◁ P : Set ⇒ Set| given by |(S ◁ P) X = Σ s : S . P s → X|. We can show that natural transformations between
containers |S ◁ P, T ◁ Q| can be represented as a pair
|Σ f : S → T , g : (s : S) → Q (f s) → P s| giving rise to the
category of containers as a subcategory of the functor category
, see
\cite{containers}. We can generalize this to containers over a given
category |ℂ|, with |S : Set| and |P : S → ℂ| with |(S ◁ P) X = Σ s : S
ℂ ( P s,X)|. We can also move to categorified containers where |S| is
a category and |Σ| is replaced by a coend.

Previously in joint work the first author has shown that the category
of containers is cartesian closed \cite{altenkirch2010higher}. The first and 3rd author have
presented the container model of type theory as a category with
families at TYPES 2021 \cite{altenkirch2021container} and the first
and second author have shown how to address
the coherence issues of this model in last year's HoTT/UF \cite{damato:cont-coh}.

The obvious question is wether the container model is closed under
|Π|-types. Our preliminary results suggest that this is not the case
but that we may have to move to a model of categorified containers as
introduced by Gylterud \cite{gylterud} which have also been the subject of last year's
HoTT/UF talk by the first author.

We use freestyle Agda in this abstract, in particular |∫ Γ| is the
category of elements of the presheaf |Γ| and (confusingly) |∫ (X : A)
H(X,X)| is the end of the profunctor |H|.

\section{Exponentials}
\label{sec:exponentials}

Let's review the simply typed case from \cite{altenkirch2010higher}
for inspiration. The key insight is that the exponential of
representable functors is a container - this can then be generalised
to showing  that the exponentials of containers, i.e. sums of
representables are a container. 

Given |P_A , P_B : Set| which represent |A , B : Set ⇒ Set|  (e.g. |A
X = P_A  → X|. We construct the container |A → B = S ◁ T| as follows:
\begin{code}
 (A => B) X 
 =⟨  universal property + Yoneda ⟩=
 ∫ Y:Set . (X → Y) → A Y → B Y
 =⟨  defn of A ⟩=
 ∫ Y:Set . (X → Y) → (P_A → Y) → B Y
 =⟨  universal property of + ⟩=
 ∫ Y:Set . (X + P_A → Y) → B Y
 =⟨  Yoneda ⟩=
 B (X + P_A)
 =⟨  defn of B ⟩=
 P_B → (X + P_A)
 =⟨  Encode + with Σ and Bool ⟩=
 P_B → Σ x : 2. ((x = 0) → X) × (x = 1) → P_A)
 =⟨  type-theoretic axiom of choice ⟩=
 Σ f : P_B → 2 . (q : P_B)(f q = 0) → X × (q : P_B)(f q = 1) → P_A
 =⟨  defn of container ⟩=
 Σ f : P_B → 2 . (q : P_B)(f q = 1) → P_A ◁ Σ (q : P_B)(f q = 0)
\end{code}

\section{|Π|-types}
\label{sec:-types}

For the dependent case we also we assume as given
\begin{code}
  Γ : Set ⇒ Set
  A : ∫ Γ ⇒ Set
  B : ∫ (Γ ▷ A) ⇒ Set
\end{code}
where |(Γ ▷ A) X = Σ γ : Γ X . A (X , γ)| We assume that all these
functors are representable, i.e. we have
\begin{code}
  P_Γ : Set
  P_A : ∫ Γ
  P_B : ∫ (Γ ▷ A) 
\end{code}
Note that on objects |∫ F = Σ X : Set . F X| and we use the projections |.X| and |.f| to project out the components.  We can now calculate |Π A B : ∫ Γ ⇒ Set|:
\begin{code}
(Π A B) : ∫ Γ → Set
(Π A B)(Y,f)
 =⟨  universal property + Yoneda ⟩=
 ∫ ((Z,g): ∫ Γ) ((h,_) : ∫ Γ((Y,f),(Z,g))) ((k,_) : A(Z,g)) → B(Z,g,k,_)
  =⟨  unfolding ⟩=
 ∫ (Z : Set)(h : Y → Z) (k : P_A.X → Z)(k ∘ P_A.f = h ∘ f))  → B(Z,h ∘ f,k,_)
\end{code}
Now we define a pushout as a HIT:
\begin{code}
 data Q : Set where
    inl : Y → Q
    inr : P_A.X → Q
    glue : (x : X) → inl (f x) = inr (P_A.f x)    
\end{code}
and use the universal property and Yoneda:
\begin{code}
 =⟨  universal property of pushout ⟩=
 = ∫ (Z : Set)(l : Q → Z) → B(Z,l ∘ inl ∘ f, l ∘ inr, _)
 =⟨  Yoneda ⟩=
 B(Q, inl ∘ f, inr, _)
 =⟨  defn of B ⟩=
 Σ(m : P_B^Y → Q)(inr = m ∘ P_B^g)(inl ∘ f = m ∘ P_B^f)
\end{code}
The question is wether we can repeat the use of the type theoretic
axiom of choice in this setting to derive a generalised container in
|∫ Γ ⇒ Set|? It seems that the pullback now pays the role of |Bool| in
the simply typed construction which suggests that we have to use
categorified container where the shapes are a category.

\bibliographystyle{plain}
%\bibliographystyle{alpha}
%\bibliographystyle{unsrt}
%\bibliographystyle{abbrv}
\bibliography{references}

%------------------------------------------------------------------------------

\end{document}
