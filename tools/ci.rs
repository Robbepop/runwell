// Copyright 2021 Robin Freyler
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Runs CI scripts locally on the users computer.
//!
//! Developers should run this script at least once before pushing to the
//! Runwell repository.
//!
//! # Usage
//!
//! In order to successfully run this script the user needs to have installed
//! the following programs on their machines:
//!
//! - git
//! - rustup
//! - cargo
//! - hunspell with en_US dictionary
//!
//! The scripts will eventually install some other Rust or Cargo components:
//!
//! - cargo-miri via rustup
//! - cargo-clippy via rustup
//! - cargo-spellcheck via cargo
//!
//! # Credits
//!
//! This quality controlling Rust script was heavily inspired by the one
//! used and provided in `stdio-utils` repository authored by Consolero:
//!
//! <https://github.com/consolero/stdio-utils-rs/blob/dev/0.1/tools/src/bin/quality-control.rs>
//!
//! Developers should run this script before pushing their pull requests to
//! the main repository to make sure that the quality of the pull request's
//! edits are in the realm of what the project accepts.

use std::{env::set_var, process::Command};

fn main() {
    // Check code formatting of all crates in the workspace.
    cargo(&["+nightly", "--locked", "fmt", "--all", "--", "--check"]);
    // Query clippy lints for the entire workspace.
    rustup(&["+nightly", "component", "add", "clippy"]);
    cargo(&[
        "+nightly",
        "--locked",
        "clippy",
        "--workspace",
        "--all-targets",
        "--all-features",
        "--",
        "-Dwarnings",
    ]);
    // Build the entire workspace with and without optimizations.
    //
    // Before building tests we need to initialize and update the
    // Git submodules.
    git(&["submodule", "update", "--init", "--recursive"]);
    cargo(&["--locked", "build", "--workspace"]);
    cargo(&["--locked", "build", "--workspace", "--release"]);
    // Test the entire workspace with and without optimizations.
    cargo(&["--locked", "test", "--workspace"]);
    cargo(&["--locked", "test", "--workspace", "--release"]);
    // Test if documentation of the entire workspace builds properly.
    // This is especially useful to detect broken intra doc links.
    //
    // We have to set `RUSTDOCFLAGS` to `-Dwarnings` so that the tool
    // errors instead of just warns.
    set_var("RUSTDOCFLAGS", "-Dwarnings");
    cargo(&[
        "--locked",
        "doc",
        "--workspace",
        "--no-deps",
        "--document-private-items",
    ]);
    // Report spelling issues in the documentation.
    cargo(&["--locked", "install", "cargo-spellcheck"]);
    cargo(&["--locked", "spellcheck", "--version"]);
    cargo(&[
        "--locked",
        "spellcheck",
        "--cfg",
        "./.config/cargo_spellcheck.toml",
        "--checkers",
        "hunspell",
        "--code",
        "1",
    ]);
    // Run miri to detect undefined behavior in Runwell crates and dependencies.
    // rustup +nightly component add miri
    rustup(&["+nightly", "component", "add", "miri"]);
    cargo(&["+nightly", "--locked", "miri", "test"]);
    // Reports code coverage using `cargo-tarpaulin`.
    cargo(&["--locked", "install", "cargo-tarpaulin"]);
    cargo(&["--locked", "tarpaulin", "--version"]);
    cargo(&["--locked", "tarpaulin", "--", "--test-threads", "1"]);
}

/// Invokes the `rustup` command with the provided arguments.
///
/// Exits the process upon errors.
fn rustup(args: &[&str]) {
    call("rustup", args)
}

/// Invokes the `cargo` command with the provided arguments.
///
/// Exits the process upon errors.
fn cargo(args: &[&str]) {
    call("cargo", args)
}

/// Invokes the `git` command with the provided arguments.
///
/// Exits the process upon errors.
fn git(args: &[&str]) {
    call("git", args)
}

/// Invokes the given command with the provided arguments.
///
/// Exits the process upon errors.
fn call(proc: &str, args: &[&str]) {
    println!("Run: {} {}", proc, args.join(" "));
    let status = Command::new(proc).args(args).status().unwrap_or_else(|_| {
        panic!("Failed to execute: {} {}", proc, args.join(" "))
    });
    match status.code() {
        Some(0) => (),
        Some(e) => std::process::exit(e),
        None => std::process::exit(1),
    }
}
