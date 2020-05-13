Idris library for Arduino
=========================

Why?
----

Mainly, just for fun.
Why not to try to use awesome language with awesome hardware?

The motivation is threefold:

- The first one was to use abilities in effects controlling that are provided by functional programming
  to have minimalistic and simple yet neat *kinda "green multitasking"*.
  It can provide fine-grained cooperative execution with no effort from the user.

- The second motivating idea grows out of mistakes that I made when playing with Arduino boards using bundled libs and C++
  or situations that I imagined to be easily made.
  This can regard to

  - using ports in wrong states;
  - mistakenly using ports for the wrong purpose (e.g. using non-PWM port as PWM);
  - using serial port when it's not ready;
  - changing global hardware state (e.g. setting pin mode to "input") in one task when using this hardware incompatibly in another task;
  - etc...;

- The third idea is an ability to express time in types.
  Since we have full bare metal control, we can try to provide compile-time realtime-ish guarantees.
  We can express time-consuming requirements of tasks and time resources of static and dynamic schedulers,
  and compile-time checks that all time requirements are satisfied and no time resources are overused.

Goals
-----

- Typesafe Idris API to Arduino primitives with

  - higher-level semantics (e.g., ``digitalWrite``'ing to ``OUTPUT`` port for a resistor turning on is considered not okay);
  - static check of correct arguments for particular boards (i.e., correctness of used pins);
  - control of correct pin states (e.g., ``digitalRead`` only on ``INPUT`` pins);
  - interrupts usability;

- A parameterized monad for cooperative multitasking with

  - sequential (lazy ``Applicative``- and ``Monad``-like) and parallel (``Alternative``-like) composition;
  - timed delay (which does not hang the whole controller but postpones a single task);
  - control that parallel tasks do not rely on same global things (e.g. pin or serial settings) or change global things incompatibly.

Non-goals
---------

Speed of execution and code simplicity in defiance of code beauty is definitely not a goal.
I'm sure some other non-goals also will be found.

Information, expressed with types
---------------------------------

Board abilities:

- which pins can be used in principle

  - as digital (binary) input and output
  - as PWM output
  - for truly analog (DAC) output
  - for analog (ADC) input

- analog resolution

  - for PWM and DAC outputs (considered to be the same)

    - which resolutions are significant, i.e. those with which values can differ in 1
    - which are available resolutions (e.g. 1 to 32 for MKR, Zero and Due, but only 8 for AVR-based)

  - for ADC inputs

    - which resolutions are significant, i.e. those with which values can differ in 1
    - which are available resolutions (e.g. 1 to 32 for MKR, Zero and Due, but only 10 for AVR-based)

- interrupts

  - which pins support interrupt handlers
  - which interrupt number correspond to which pin

- pins for built-in I/O

  - built-in LED (only one?)
  - UARTs: ``Vect n UartPins``, UART pins: TX, RX
  - I2Cs: ``Vect n I2cPins``, I2C pins: SDA, SCL
  - SPIs: ``Vect n SPIs``, SPI pins: MISO, MOSI, SCK, SS

Board state:

- which digital pins are set as input, which are as output;
- bit resolution of analog-ish pins;
- status of serial (begun, ended);
- ...

