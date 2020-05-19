# Contributing to Manticore

First, thanks for your interest in contributing to Manticore! We welcome and
appreciate all contributions, including bug reports, feature suggestions,
tutorials/blog posts, and code improvements.

If you're unsure where to start, we recommend our [`easy`](https://github.com/trailofbits/manticore/issues?q=is%3Aissue+is%3Aopen+label%3Aeasy) and [`help wanted`](https://github.com/trailofbits/manticore/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22)
issue labels.

## Bug reports and feature suggestions

Bug reports and feature suggestions can be submitted to our [issue
tracker](https://github.com/trailofbits/manticore/issues). For bug reports,
attaching the binary that caused the bug will help us in debugging and
resolving the issue quickly. If you find a security
vulnerability, do not open an issue; email opensource@trailofbits.com
instead.

## Questions

Questions can be submitted to the [discussion page](https://github.com/trailofbits/manticore/discussions), but you may get a faster
response if you ask in our [chat room](https://empireslacking.herokuapp.com/)
(in the #manticore channel).

## Legal
For legal reasons, we require contributors to sign our [Contributor License Agreement](https://cla-assistant.io/trailofbits/manticore).
This will be automatically checked as part of our CI. 

## Code

Manticore uses the pull request contribution model. Please make an account on
Github, fork this repo, and submit code contributions via pull request. For
more documentation, look [here](https://guides.github.com/activities/forking/).

Some pull request guidelines:

- We use the [`black`](https://black.readthedocs.io/en/stable/index.html)
  auto-formatter to enforce style conventions in Manticore. To ensure your code
  is properly formatted, run `black .` in the Manticore directory before
  committing. Although unlikely, if you are still having trouble with getting
  your code to pass formatting, check that you have the same version of `black`
  installed as what is used in the CI.
- We use the [`mypy`](https://github.com/python/mypy) static typing tool to
  catch inconsistencies in the code base. At the time of this writing, we
  only check the [manticore](./manticore) directory for inconsistencies and do
  not yet enforce new contributions to include type hints. However, we greatly
  appreciate if you do include/add them in any code that you touch in your PR!
  Though, remember the next guideline if you are adding many type-hints, and
  ask for input on how to organize the addition of a massive amount of type
  hints. Check the CI configuration for the exact version of `mypy`.
- Minimize irrelevant changes (formatting, whitespace, etc) to code that would
  otherwise not be touched by this patch. Save formatting or style corrections
  for a separate pull request that does not make any semantic changes.
- When possible, large changes should be split up into smaller focused pull
  requests.
- Fill out the pull request description with a summary of what your patch does,
  key changes that have been made, and any further points of discussion, if
  applicable.
- Title your pull request with a brief description of what it's changing.
  "Fixes #123" is a good comment to add to the description, but makes for an
  unclear title on its own.

### Development Environment

Instructions for installing a development version of Manticore can be found in
our [wiki](https://github.com/trailofbits/manticore/wiki/Hacking-on-Manticore#developer-installation).
