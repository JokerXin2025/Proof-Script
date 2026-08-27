
import ProofScript.Extension.Component.Core

open Lean
open Lean.Elab.Command (CommandElabM liftIO)

namespace ProofScript.Extension


def latexPreamble :=
  "\\documentclass[border=2pt,varwidth]{standalone}\n" ++
  "\\def\\pgfsysdriver{pgfsys-dvisvgm.def}\n" ++
  "\\usepackage{amsmath,amssymb,bm,mathrsfs}\n" ++
  "\\usepackage{tikz,graphicx,booktabs,array,longtable,tabularx,multirow}\n" ++
  "\\usetikzlibrary{cd}\n"

private def cleanSvg (raw : String) : String :=
  let lines := raw.splitOn "\n"
  let afterStart := lines.dropWhile
    fun line => !(line.startsWith "<svg")
  let kept :=
    match afterStart.findIdx? (fun line => line.startsWith "</svg>") with
    | some index => afterStart.take (index + 1)
    | none => afterStart
  String.intercalate "\n" kept

private def processError  (name : String)
                          (output : IO.Process.Output)
                          : String :=
  let details :=
    if output.stderr.trimAscii.isEmpty then output.stdout
    else output.stderr
  s!"{name} failed with exit code {output.exitCode}:\n{details}"

open IO.FS in
def compileLatexToSvg (source : String) : IO String := do
  withTempDir fun dir => do
    let tex := latexPreamble ++ "\\begin{document}\n" ++ source ++ "\n\\end{document}\n"
    writeFile (dir / "component.tex") tex
    let latex ← IO.Process.output {
      cmd := "latex"
      args := #["-interaction=nonstopmode", "-halt-on-error", "component.tex"]
      cwd := some dir
    }
    unless latex.exitCode == 0 do
      throw <| IO.userError (processError "latex" latex)
    let dvisvgm ← IO.Process.output {
      cmd := "dvisvgm"
      args := #["--no-fonts", "--exact", "-o", "component.svg", "component.dvi"]
      cwd := some dir
    }
    unless dvisvgm.exitCode == 0 do
      throw <| IO.userError (processError "dvisvgm" dvisvgm)
    cleanSvg <$> readFile (dir / "component.svg")

private def addLatexComponent (metadataStx : Syntax) (codeStx : TSyntax `str) : CommandElabM Unit := do
  let metadata ← match parseComponentMetadata metadataStx with
    | .ok metadata => pure metadata
    | .error message => throwErrorAt metadataStx message
  let svg ← liftIO <| compileLatexToSvg codeStx.getString
  let labels := match metadata.label with
    | some label => #[(ReferenceKind.figure, label)]
    | none => #[]
  addPageComponent codeStx.raw (.latex { metadata, source := codeStx.getString, svg }) labels

syntax "#latex" componentMeta str : command

open Lean.Elab.Command in
elab_rules : command
  | `(command| #latex $metadata:componentMeta $code:str) =>
      addLatexComponent metadata.raw code


end ProofScript.Extension
