.. raw:: html

  <p>
    <a href="https://relicprotocol.com">
       <h1 align="center">
       <p><img src="https://relicprotocol.com/logo.svg" height="32" /></p>
          <p>Circuits</p>
       </h1>
    </a>
  </p>


The goal of `Relic Protocol`_ is to provide access to historical Ethereum state on-chain. To this end, Relic Protocol stores a Merkle tree root for groups of 8192 block headers. The only way to verify the validity of the Merkle tree roots is to have access to all 15 milllion historical block headers, but this would be too expensive on-chain. Relic Protocol uses a zk-SNARK circuit, specifically an UltraPlonK circuit based on the work by `Matter Labs`_, to calculate a proof off-chain that can be cheaply verified on-chain.

.. _Matter Labs: https://github.com/matter-labs
.. _Relic Protocol: https://relicprotocol.com

=====
Usage
=====

``build-vk.sh`` is included which will build the circuit verification keys. You must first download the `universal setup file`_.

.. _universal setup file: https://universal-setup.ams3.digitaloceanspaces.com/setup_2%5E23.key

=======
License
=======

Documentation and source code in the following directories is licensed for reference use only. You may download it, read it, and/or build it only for the purposes of determining its correctness and security. You may not distribute it or use it in any derivative works without permission of Theori, Inc.

- proof_generator

Documentation and source code of any unmodified dependencies are licensed according to their included LICENSE files.

- bellman
- franklin_crypto

