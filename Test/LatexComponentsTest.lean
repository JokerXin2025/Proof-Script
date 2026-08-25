import ProofScript

#LaTeX (title := "Arbitrary LaTeX", label := "page-latex", placement := "center") r#"
\begin{tikzpicture}
  \node[draw] (A) at (0,0) {$A$};
  \node[draw] (B) at (2,0) {$B$};
  \draw[->] (A) -- (B);
\end{tikzpicture}
"#

#figure (title := "Image resource", label := "page-figure", width := "wide")
  "assets/example-diagram.png"

#theorem latexComponentsInProof (P : Prop) (h : P) : P := script
  tikz (title := "Inline TikZ", label := "inline-tikz") r#"
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  "#
  figure (title := "Inline figure", label := "inline-figure") r#"
    \begin{figure}
      \centering
      \fbox{\rule{0pt}{10mm}\rule{20mm}{0pt}}
    \end{figure}
  "#
  table (title := "Inline table", label := "inline-table") r#"
    \begin{table}
      \begin{tabular}{lr}
        X & 1 \\
      \end{tabular}
    \end{table}
  "#
  provide h

example (P : Prop) (h : P) : P := script
  tikz r#"
    \begin{tikzpicture}
      \draw (0,0) circle (2pt);
    \end{tikzpicture}
  "#
  provide h

#page_end
