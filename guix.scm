; SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
;; guix.scm — GNU Guix package definition for ephapax
;; Usage: guix shell -f guix.scm

(use-modules (guix packages)
             (guix build-system gnu)
             (guix licenses))

(package
  (name "ephapax")
  (version "0.1.0")
  (source #f)
  (build-system gnu-build-system)
  (synopsis "ephapax")
  (description "ephapax — part of the hyperpolymath ecosystem.")
  (home-page "https://github.com/hyperpolymath/ephapax")
  (license ((@@ (guix licenses) license) "PMPL-1.0-or-later"
             "https://github.com/hyperpolymath/palimpsest-license")))
