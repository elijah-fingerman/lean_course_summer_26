import VersoSlides
import lecture1.lecture1

open VersoSlides

-- Embed the shared course theme so the generated deck remains styled and works offline.
def lectureTheme : CssFile where
  filename := "lecture-theme.css"
  contents := ⟨include_str "./theme.css"⟩

def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := "white"
      transition := "fade"
      width := 1280
      height := 720
      margin := 0.06
      controls := true
      progress := true
      slideNumber := true
      hash := true
      center := true
      extraCss := #[lectureTheme]
      outputDir := "LectureNotes/lecture1/output"
    })
    (doc := %doc lecture1.lecture1)
