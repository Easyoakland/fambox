# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## Changed
- Simplify `FamBoxBuilder`

## Added
- Implement most standard traits that apply to `FamBox` variants

## Fixed
- `FamBoxBuilder` behavior corrected for when fam is empty.
- `Deserialize` bounds relaxed.

## [0.1.2] - 2024-05-15

### Added
- `FamBoxBuilder` allows building a `FamBoxOwned` one element at a time.

### Fixed
- `FamBoxOwned::from_fn` doesn't leak memory if the provided callback panics.
- `FamBoxOwned` calls the drop implementations of the header `H` and elements `H::Element`
- `FamBoxOwned` doesn't allocate a temporary vector on `Deserialize`.

### Removed
- `smallvec` is no longer a dependency

## [0.1.1] - 2024-05-15

### Fixed
- docs.rs features on build

## [0.1.0] - 2024-05-15

### Added
Initial Release