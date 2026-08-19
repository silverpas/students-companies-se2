# Students&Companies (S&C) — SE2 Project 2024/2025

Software Engineering 2 project @ Politecnico di Milano, A.Y. 2024/2025.

**Authors:** Simone Molinari, Davide Orizio, Silvia Pasini

## About

Students&Companies (S&C) is a web platform designed to ease the matching process between
students looking for internships and companies offering them. The platform matches students
with internships based on skills, experience, and career goals — as described in students'
CVs — against company project descriptions, and supports the full internship lifecycle:
publishing internships, applying, interviews and selection, feedback, and university
monitoring of ongoing internships.

## Repository structure

- [`RASD/`](RASD) — Requirements Analysis and Specification Document (LaTeX source, use case
  diagrams, sequence diagrams, and formal analysis using Alloy).
- [`DD/`](DD) — Design Document (LaTeX source, architectural design, UI design, requirements
  traceability, implementation/integration/test plan).
- [`DeliveryFolder/`](DeliveryFolder) — Final delivered PDFs (`RASDv1.pdf`, `DDv1.pdf`).

## Building the documents

Each document is a standalone LaTeX project. To build, e.g., the RASD:

```bash
cd RASD/LaTeXCode
pdflatex RASD.tex
pdflatex RASD.tex   # run twice for references/TOC
```

Same procedure applies for `DD/LaTeXCode/DD.tex`.

## License

This project is licensed under the terms of the [GNU General Public License v3.0](LICENSE).
