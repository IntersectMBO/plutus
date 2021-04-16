.. _playground-overview:

The Marlowe Playground
======================

This tutorial gives an overview of the `Marlowe Playground`_, an online
tool that allows users to create, to analyse, to interact with and to
simulate the operation of embedded Marlowe contracts.

Introducing the Marlowe Playground
----------------------------------

For Marlowe to be usable in practice, users need to be able to
understand how contracts will behave once deployed to the blockchain,
but without doing the deployment. We can do that by simulating their
behaviour off-chain, interactively stepping through the evaluation of a
contract in the browser-based tool, the Marlowe Playground, a web tool
that supports the interactive construction, revision, and simulation of
smart-contracts written in Marlowe.

Contracts can be authored in four different ways in the Playground. We
can write directly in Marlowe, or use the Blockly representation of
Marlowe. Marlowe is also embedded in Haskell and JavaScript, and we can
author contracts in these languages and then convert ("compile") them to
Marlowe in the Playground.

.. image:: images/authoring.png
   :alt: Authoring contracts in the Marlowe Playground

Once a contract has been written in Blockly, Haskell, or JavaScript, we
can move to the Simulator to analyse and simulate the contract.

Work from the Playground can be saved as a github gist. This saves, as a
**project**, everything in the Playground: not only the contracts but
the current state of the simulation, the logs and so on. Projects can be
reloaded or duplicated at a later time. Even without using github the
project is saved between sessions, but this is *volatile*, and will be
lost if browser caches are updated.

The rest of this section will cover the operation of the Playground in
more detail. In later sections, two *experimental* features, which are
under active development, are also covered: :ref:`Actus
Labs <actus-labs>` and the :ref:`Wallet-level
simulation <wallets-simulation>`.

We use **bold** type for buttons and other components in what follows.

Getting started
---------------

The landing page for the Marlowe Playground looks like this

.. image:: images/landing-page.png
   :alt: The landing page for the Playground

The title bar has, at the right-hand side, links to this tutorial and
the Actus Labs feature, and the **main menu** operations are shown below
this.

-  **New Project** This clears the existing project, and creates a new
   one, in a coding environment of the user’s choice:

.. image:: images/initial-env.png
   :alt: Choosing the initial environment

-  **Open Project** This opens a project that has been saved previously.
   See the section on `Saving and Opening
   Projects <#_saving_and_opening_projects>`_ below for more details on
   setting this up.

-  **Open Example** This will load an example into the existing project,
   in the environment chosen by the user.

.. image:: images/open-example.png
   :alt: Opening an example

-  **Rename Project** Renames a project: the name is shown in the centre
   of the title bar.

-  **Save Project** Saves a project. See the section `Saving and Opening
   Projects <#_saving_and_opening_projects>`_ below.

-  **Save as New Project** Saves the current project with a new name.

The program editor used in the Playground is the Monaco editor
https://microsoft.github.io/monaco-editor/ and many of its features are
available, including the menu available on right-click.

The Haskell Editor: developing embedded contracts
-------------------------------------------------

The editor supports the development of Marlowe contracts described in
Haskell. We can use Haskell to make contract definitions more readable
by using Haskell definitions for sub-components, abbreviations, and
simple template functions. The Haskell editor is shown in the following
image.

.. image:: images/haskell-editor.png
   :alt: The Haskell editor

The Haskell editor is open here on the Escrow example contained in the
examples. To describe a Marlowe contract in the editor, we have to
define a top-level value ``contract`` of type ``Contract``; it is this
value that is converted to pure Marlowe with the **Compile** button (in
the top right-hand corner). If compilation is successful, the compiled
code is shown in an overlay (which can be minimised):

.. image:: images/haskell-compiled.png
   :alt: Haskell code compiled to Marlowe

On successful compilation the result can be sent to the simulator or to
Blockly: these options are provided by the **Send to Simulator** and
**Send to Blockly** buttons in the top right-hand corner of the page.

If the contract cannot successfully be converted to Marlowe, the errors
are also shown in an overlay:

.. image:: images/haskell-errors.png
   :alt: Errors in compiling Haskell code to Marlowe

The JavaScript Editor: developing embedded contracts
----------------------------------------------------

The editor supports the development of Marlowe contracts described in
JavaScript, too. We can use JavaScript to make contract definitions more
readable by using JS definitions for sub-components, abbreviations, and
simple template functions. The JS editor is shown in the following
image.

.. image:: images/js-editor.png
   :alt: The JavaScript editor

The JS editor is open here on the Escrow example contained in the
examples. To describe a Marlowe contract in the editor, a value of the
type ``Contract`` must be returned as result of the provided function by
using the instruction ``return``.

.. image:: images/js-editor-cont.png
   :alt: The value returned by ``return`` defines the contract.

The editor supports auto-complete, error checking during editing, and
information about bindings on mouse over. In particular, using mouse
over on any of the imported bindings will show its type (in TypeScript).

When you click the **Compile** button (in the top right-hand corner),
the code in the editor is executed, and the JSON object returned by the
function resulting from the execution is parsed into an actual Marlowe
contract that can then be sent to the Simulation tab where it can be
simulated.

If compilation is successful, the compiled code is shown in an overlay
(which can be minimised):

.. image:: images/js-compiled.png
   :alt: JS code compiled to Marlowe

On successful compilation the result can be sent to the simulator using
the **Send to Simulator** button in the top right-hand corner of the
page.

If the contract cannot successfully be converted to Marlowe, the errors
are also shown in an overlay:

.. image:: images/js-error.png
   :alt: Errors in compiling JS code to Marlowe

Developing contracts in Blockly
-------------------------------

The playground provides a mechanism for creating and viewing contracts
in a visual form, rather than in text. This is discussed in this earlier
section on :ref:`Blockly <playground-blockly>`.

Developing contracts in Marlowe
-------------------------------

It is also possible to create contracts in "raw" Marlowe too, and this
is performed in the simulation environment. Marlowe is edited in the
Monaco editor, and this gives automatic formatting (on right click) and
supports **holes** too.

.. image:: images/marlowe-editor.png
   :alt: Editing Marlowe: using holes

Holes allow a program to be built top-down. Clicking the lightbulb next
to a hole presents a completion menu, in each case replacing each sub
component by a new hole. For example, choosing ``Pay`` to fill the
top-level hole will result in this:

.. image:: images/marlowe-hole-fill.png
   :alt: Editing Marlowe: filling a hole

Holes can be combined with ordinary text editing, so that you can use a
mixture of bottom-up and top-down constructs in building Marlowe
contracts. Moreover, contracts with holes can be transferred to and from
Blockly: holes in Marlowe become literal holes in Blockly. To transfer
to Blockly use the **View in Blockly Editor** in the top right-hand
corner of the screen.

Simulating Marlowe contracts
----------------------------

However a contract is written, when it is sent to simulation this is the
view seen first.

.. image:: images/simulation-tab.png
   :alt: The Simulation pane

The code shown here presents whatever of the contract remains to be
simulated, and the pane at the foot gives data about the simulation, as
well as giving access to *static analysis* for the contract (from its
current state).

Simulation is started by clicking the **Start simulation** button, and
once this is done, the available actions that will advance the contract
are presented;

.. image:: images/available-actions.png
   :alt: The actions available

In this case there are two potential actions: Alice can make a deposit,
or the slot (time) can advance to ``10`` at which the wait for a deposit
times out. Two other generic actions can be taken too

-  **Undo** will undo the last action made in the simulator. This means
   that we can explore a contract interactively, making some moves,
   undoing some of them, and then proceeding in a different direction.

-  **Reset** will reset the contract and its state back to their initial
   values: the full contract and an empty state. It also *stops* the
   simulation.

For our example, let us select for Alice to make the deposit of 450
lovelace. We can do that with the **+** button next to this input. After
doing that we see

.. image:: images/simulation2.png
   :alt: Simulation step 2

Where we see at the foot of the screen that the deposit has taken place.

This remains in view if we then make Alice’s and then Bob’s choice. Note
also that the current state of the contract is shown in the main part of
the window, and indeed we are waiting at this stage for a choice from
Alice.

If Alice and Bob make different choices we then see

.. image:: images/simulation3.png
   :alt: Simulation step 3

and at this point in the evolution of the contract we are awaiting a
choice from Carol to arbitrate the outcome.

Oracle simulation
-----------------

As we noted earlier in the section on `??? <#_oracles>`_, the
Playground provides oracle values to simulations for the role
``"kraken"``. When the simulation reaches the point of simulating this
construct

.. image:: images/oracles1.png
   :alt: Asking for an oracle value

then the value is *pre-filled* in the simulation like this:

.. image:: images/oracles2.png
   :alt: Providing an oracle value

Saving and Opening Projects
---------------------------

Projects can be saved on github, and so when you first save a project
you will be prompted thus:

.. image:: images/github1.png
   :alt: Prompt to login to github

and, if you choose to **Login** there, you will be taken to a login
screen for github:

.. image:: images/github2.png
   :alt: Logging in to github

When you opt to **Open Project** you will be presented with a choice
like this:

.. image:: images/github3.png
   :alt: Open project choice

The Marlowe Playground does not provide a mechanism for deleting
projects, but this can be done directly on github.

Analysing a contract
--------------------

The static analysis of a contract is performed by selecting the **Static
analysis** tab in the pane at the foot of the page.

.. image:: images/static-analysis.png
   :alt: Static analysis

Clicking the **Analyse for warnings** button results in the current
contract *in the current state* being analysed. The result is either to
say that the contract passed all the tests, or to explain how it fails,
and giving the sequence of transactions that lead to the error. As an
exercise try this with the ``Escrow`` contract, changing the initial
deposit from Alice to something smaller than 450 lovelace. More details
are given in the section on
:ref:`static analysis <static-analysis>` below.

The **Analyse reachability** button will check whether any parts of a
contract will never be executed, however participants interact with it.

Use the Marlowe Playground to interact with the ``escrow`` contract in
the various scenarios discussed in the tutorial on :ref:`using
Marlowe <using-marlowe>`.

Explore making some changes to the contract and interactions with those
modified contracts.

Use the Marlowe Playground to explore the other examples presented in
there: the deposit incentive contract, and the crowd-funding example.
