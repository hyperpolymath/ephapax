# SPDX-License-Identifier: PMPL-1.0-or-later
# config.ncl - Ephapax Playground Configuration
# Type-safe configuration using Nickel
# See: https://nickel-lang.org

{
  # Project metadata
  project = {
    name = "ephapax-playground",
    version = "1.0.0",
    description = "Playground for Ephapax Playground",
    license = "PMPL-1.0-or-later",
    author = "Jonathan D.A. Jewell",
    repository = "https://github.com/hyperpolymath/ephapax-playground",
  },

  # Documentation configuration
  docs = {
    readme = "README.adoc",
  },

  # Development settings
  development = {
    default_tasks = [
      "build",
      "lint",
      "fmt",
      "test",
    ],
  },

  # Computed values
  full_name = project.name ++ " v" ++ project.version,
}
