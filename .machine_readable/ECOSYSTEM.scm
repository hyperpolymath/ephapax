;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm for ephapax
;; Media Type: application/vnd.ecosystem+scm

(ecosystem
  (version "1.0")
  (name "ephapax")
  (type "programming-language")
  (purpose "Language exploring linear types and one-time execution guarantees")

  (position-in-ecosystem
    (domain "programming-languages")
    (role "Experimental language within the nextgen-languages monorepo")
    (maturity "concept"))

  (related-projects
    ((name . "nextgen-languages")
     (relationship . part-of)
     (nature . "Monorepo for experimental language projects"))))
