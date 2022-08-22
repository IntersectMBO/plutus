ADR 1: Record architectural decisions
=======================================

Date: 2022-06-08

Authors
---------

koslambrou <konstantinos.lambrou@iohk.io>

Status
------

Accepted

Context
-------

We are in search for a means to document our architectural and design decisions
for all of our components.
In order to do that, there is practice called architectural decision records ("ADR"),
that we can integrate into our workflow.

This does not replace actual architecture documentation, but provides people who are contributing:

* the means to understand architectural and design decisions that were made
* a framework for proposing changes to the current architecture

For each decision, it is important to consider the following factors:

* what we have decided to do
* why we have made this decision
* what we expect the impact of this decision to be
* what we have learned in the process

As we're already using `rST <https://docutils.sourceforge.io/rst.html>`_,
`Sphinxdoc <https://www.sphinx-doc.org/en/master/>`_ and
`readthedocs <https://readthedocs.org/>`_, it would be practical to
integrate these ADRs as part of our current documentation infrastructure.

Decision
--------

* We will use ADRs to document, propose and discuss
  any important or significant architectural and design decisions.

* The ADR format will follow the format described in `Implications`_ section.

* We will follow the convention of storing those ADRs as rST or Markdown formatted
  documents stored under the `docs/adr` directory, as exemplified in Nat Pryce's
  `adr-tools <https://github.com/npryce/adr-tools>`_. This does not imply that we will
  be using `adr-tools` itself, as we might diverge from the proposed structure.

* We will keep rejected ADRs

* We will strive, if possible, to create an ADR as early as possible in relation to the actual
  implementation.

Implications
------------

ADRs should be written using the template described in the `ADR template`_ which comes from
Chapter 6.5.2 (*A Template for Documenting Architectural Decisions*) of
*Documenting Software Architectures: Views and Beyond (2nd Edition)*.

However, the mandatory sections are *Title*, *Status*, *Issue/Context*, *Decision*, *Implications/Consequences*.
The rest are optional.

Another good reference is the article
`Architecture Decision Records <https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions>`_
by Michael Nygard (Nov. 15, 2011).

ADR template
^^^^^^^^^^^^

What follows is the ADR format (adapted from the book).

+----------------------+---------------------------------------------------------------------------+
| Section              | Description                                                               |
+======================+===========================================================================+
| Title                | These documents have names that are short noun phrases.                   |
|                      |                                                                           |
|                      | For example, "ADR 1: Deployment on Ruby on Rails 3.0.10"                  |
|                      | or "ADR 9: LDAP for Multitenant Integration"                              |
+----------------------+---------------------------------------------------------------------------+
| Authors              | List each author's name and email.                                        |
+----------------------+---------------------------------------------------------------------------+
| Status               | State the status of the decision, such as "draft" if the decision is      |
|                      | still being written, as "proposed" if the project stakeholders haven't    |
|                      | agreed with it yet, "accepted" once it is agreed. If a later ADR changes  |
|                      | or reverses a decision, it may be marked as "deprecated" or "superseded"  |
|                      | with a reference to its replacement. (This is not the status of           |
|                      | implementing the decision.)                                               |
+----------------------+---------------------------------------------------------------------------+
| Issue (or context)   | This section describes the architectural design issue being addressed.    |
|                      | This description should leave no questions as to why this issue needs to  |
|                      | be addressed now. The language in this section is value-neutral. It is    |
|                      | simply describing facts.                                                  |
+----------------------+---------------------------------------------------------------------------+
| Decision             | Clearly state the solution chosen. It is the selection of one of the      |
|                      | positions that the architect could have taken. It is stated in full       |
|                      | sentences, with active voice. "We will …"                                 |
+----------------------+---------------------------------------------------------------------------+
| Tags                 | Add one or more tags to the decision. Useful for organizing the set of    |
|                      | decision.                                                                 |
+----------------------+---------------------------------------------------------------------------+
| Assumptions          | Clearly describe the underlying assumptions in the environment in which a |
|                      | decision is being made. These could be cost, schedule, technology, and so |
|                      | on. Note that constraints in the environment (such as a list of accepted  |
|                      | technology standards, an enterprise architecture, or commonly employed    |
|                      | patterns) may limit the set of alternatives considered.                   |
+----------------------+---------------------------------------------------------------------------+
| Argument             | Outline why a position was selected. This is probably as important as the |
|                      | decision itself. The argument for a decision can include items such as    |
|                      | implementation cost, total cost of ownership, time to market, and         |
|                      | availability of required development resources.                           |
+----------------------+---------------------------------------------------------------------------+
| Alternatives         | List alternatives (that is, options or positions) considered.             |
|                      |                                                                           |
|                      | Explain alternatives with sufficient detail to judge their suitability;   |
|                      | refer to external documentation to do so if necessary. Only viable        |
|                      | positions should be described here. While you don’t need an exhaustive    |
|                      | list, you also don’t want to hear the question “Did you think about... ?” |
|                      | during a final review, which might lead to a loss of credibility and a    |
|                      | questioning of other architectural decisions. Listing alternatives        |
|                      | espoused by others also helps them know that their opinions were heard.   |
|                      | Finally, listing alternatives helps the architect make the right          |
|                      | decision, because listing alternatives cannot be done unless those        |
|                      | alternatives were given due consideration.                                |
+----------------------+---------------------------------------------------------------------------+
| Implications         | Describe the decision’s implications. For example, it may                 |
| (or consequences)    |                                                                           |
|                      |   * Introduce a need to make other decisions                              |
|                      |   * Create new requirements                                               |
|                      |   * Modify existing requirements                                          |
|                      |   * Pose additional constraints to the environment                        |
|                      |   * Require renegotiation of scope                                        |
|                      |   * Require renegotiation of the schedule with the customers              |
|                      |   * Require additional training for the staff                             |
|                      |                                                                           |
|                      | Clearly understanding and stating the implications of the decisions has   |
|                      | been a very effective tool in gaining buy-in. All consequences should be  |
|                      | listed here, not just the "positive" ones. A particular decision may have |
|                      | positive, negative, and neutral consequences, but all of them affect the  |
|                      | team and project in the future.                                           |
+----------------------+---------------------------------------------------------------------------+
| Related Decisions    | List decisions related to this one. Useful relations among decisions      |
|                      | include causality (which decisions caused other ones), structure (showing |
|                      | decisions’ parents or children, corresponding to architecture elements at |
|                      | higher or lower levels), or temporality (which decisions came before or   |
|                      | after others).                                                            |
+----------------------+---------------------------------------------------------------------------+
| Related Requirements | Map decisions to objectives or requirements, to show accountability. Each |
|                      | architecture decision is assessed as to its contribution to each major    |
|                      | objective. We can then assess how well the objective is met across all    |
|                      | decisions, as part of an overall architecture evaluation.                 |
+----------------------+---------------------------------------------------------------------------+
| Affected Artifacts   | List the architecture elements and/or relations affected by this          |
|                      | decision. You might also list the effects on other design or scope        |
|                      | decisions, pointing to the documents where those decisions are described. |
|                      | You might also include external artifacts upstream and downstream of the  |
|                      | architecture, as well as management artifacts such as budgets and         |
|                      | schedules.                                                                |
+----------------------+---------------------------------------------------------------------------+
| Notes                | Capture notes and issues that are discussed during the decision process.  |
|                      | They can be links to a external document, a PR, a Github issue, etc.      |
+----------------------+---------------------------------------------------------------------------+
