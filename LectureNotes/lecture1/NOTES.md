# Lecture notes

The first lecture is a VersoSlides presentation based on the notes from 3 July 2026.
Its Lean examples are elaborated when the deck is built.

Build and generate the slides from the repository root:

```text
lake build lecture1-slides
lake exe lecture1-slides
```

The generated presentation is written to `LectureNotes/lecture1/output/index.html`.
Serve that directory with any local HTTP server to present it.

Lecture 2 follows the same layout:

```text
lake build lecture2-slides
lake exe lecture2-slides
```

Its output is written to `LectureNotes/lecture2/output/index.html`.
