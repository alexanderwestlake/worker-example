import { Provable, ZkProgram, SelfProof, provable, AccountUpdateForest, AccountUpdate, TokenContract, PublicKey, Struct, Bool, Field, method, UInt64 } from "o1js";

import {
  addRandomTile,
  addRandomTile2,
  applyOneMoveCircuit,
  applyOneMoveCircuit2,
  BoardArray,
  Direction,
  GameBoard,
  GameBoardWithSeed,
  MAX_MOVES2,
  MAX_PARALLEL,
} from "./game2048ZKLogic";

export const Game2048ZKProgram = ZkProgram({
  name: "Game2048ZKProgram",
  publicOutput: BoardArray,

  methods: {
    baseCase: {
      privateInputs: [BoardArray, Direction],

      async method(boards: BoardArray, directions: Direction) {
        let initBoard = boards.value[0];
        let newBoard = boards.value[1];

        let currentBoard = initBoard.getBoard();
        let currentSeed = initBoard.getSeed();

        for (let i = 0; i < MAX_MOVES2; i++) {
          let nextBoard = applyOneMoveCircuit2(
            currentBoard,
            directions.value[i],
          );

          let needAddTile = nextBoard.hash().equals(currentBoard.hash()).not();

          currentBoard = nextBoard;
          [currentBoard, currentSeed] = addRandomTile2(
            currentBoard,
            currentSeed,
            needAddTile,
          );
        }
        Provable.log(currentBoard);
        Provable.log(newBoard);
        for (let j = 0; j < 16; j++) {
          currentBoard.cells[j].assertEquals(newBoard.board.cells[j]);
        }
        newBoard.seed.assertEquals(currentSeed);
        return { publicOutput: boards };
      },
    },

    /**
     * Inductive Step: Recursively verifies groups of proofs by comparing their
     * initial and terminal states to verify that there is a continuous transition
     * between them (eg A->E, E->I. We compare E, E and return proof that A->I).
     */
    inductiveStep: {
      privateInputs: [SelfProof, SelfProof],

      async method(
        proof1: SelfProof<void, BoardArray>,
        proof2: SelfProof<void, BoardArray>,
      ) {
        Provable.log(proof1);
        Provable.log(proof2);
        //verify both earlier proofs
        proof1.verify();
        proof2.verify();

        Provable.log("Verified both proofs.");

        const proof1board1 = proof1.publicOutput.value[0];
        const proof1board2 = proof1.publicOutput.value[1];
        const proof2board1 = proof2.publicOutput.value[0];
        const proof2board2 = proof2.publicOutput.value[1];

        //compare seeds
        proof1board2.seed.assertEquals(proof2board1.seed);
        Provable.log("Verified both seeds.");

        //compare cells
        for (let c = 0; c < 16; c++) {
          proof1board2.board.cells[c].assertEquals(proof2board1.board.cells[c]);
        }
        Provable.log("Verified all cells.");

        //construct new BoardArray capturing the fact that we now have a proof for A->C from A->B, B->C
        const boardArr = [proof1board1, proof2board2];
        const retArray = new BoardArray(boardArr);
        Provable.log(boardArr);

        Provable.log("Created return array.");
        Provable.log(retArray);

        return { publicOutput: retArray };
      },
    },
  },
});

export class BoardEvent extends Struct({
  board: GameBoardWithSeed,
}) {}

export class ProofEvent extends Struct({
  proof: SelfProof,
}) {}

export class AddValue extends Struct({
  value: UInt64,
  limit: UInt64,
}) {
  toState() {
    return [this.value.value, this.limit.value];
  }
}

export async function stateOperation(currentBoard: GameBoard, currentSeed: Field, direction: Field) {
  let nextBoard = applyOneMoveCircuit2(
    currentBoard,
    direction,
  );

  let needAddTile = nextBoard.hash().equals(currentBoard.hash()).not();

  currentBoard = nextBoard;
  return addRandomTile2(
    currentBoard,
    currentSeed,
    needAddTile,
  );
}

export class ZKProgramProof extends ZkProgram.Proof(Game2048ZKProgram) {}

export class ZKContract extends TokenContract {

  init() {
    super.init();
    //this.limit.set(UInt64.from(limit));
  }

  async approveBase(forest: AccountUpdateForest) {
    throw Error("transfers are not allowed");
  }

  events = {
    addValue: BoardEvent,
  };

  @method async addOne(address: PublicKey, initBoard: GameBoardWithSeed, direction: Field) {
    let currentBoard = initBoard.getBoard();
    let currentSeed = initBoard.getSeed();
    await stateOperation(currentBoard, currentSeed, direction);
  }

  @method async addMany(address: PublicKey, initBoard: GameBoardWithSeed, directions: Direction) {
    let currentBoard = initBoard.getBoard();
    let currentSeed = initBoard.getSeed();

    for (let i = 0; i < MAX_MOVES2; i++) {
      [currentBoard, currentSeed] = await stateOperation(currentBoard, currentSeed, directions.value[i]);
    }
  }

  @method async mergeProofs(proof1: ZKProgramProof, proof2: ZKProgramProof){
    proof1.verify();
    proof2.verify();

    const proof1board1 = proof1.publicOutput.value[0];
    const proof1board2 = proof1.publicOutput.value[1];
    const proof2board1 = proof2.publicOutput.value[0];
    const proof2board2 = proof2.publicOutput.value[1];

    //compare seeds
    proof1board2.seed.assertEquals(proof2board1.seed);
    Provable.log("Verified both seeds.");

    //compare cells
    for (let c = 0; c < 16; c++) {
      proof1board2.board.cells[c].assertEquals(proof2board1.board.cells[c]);
    }
    Provable.log("Verified all cells.");

    //construct new BoardArray capturing the fact that we now have a proof for A->C from A->B, B->C
    const boardArr = [proof1board1, proof2board2];
    const retArray = new BoardArray(boardArr);
    Provable.log(boardArr);
  }

  /*async createAddValue(address: PublicKey, addValue: AddValue) {
    const tokenId = this.deriveTokenId();
    const update = AccountUpdate.createSigned(address, tokenId);
    update.account.balance.getAndRequireEquals().assertEquals(UInt64.from(0));
    this.internal.mint({
      address: address,
      amount: addValue.value,
    });
    const state = addValue.toState();
    update.body.update.appState = [
      { isSome: Bool(true), value: state[0] },
      { isSome: Bool(true), value: state[1] },
      { isSome: Bool(false), value: Field(0) },
      { isSome: Bool(false), value: Field(0) },
      { isSome: Bool(false), value: Field(0) },
      { isSome: Bool(false), value: Field(0) },
      { isSome: Bool(false), value: Field(0) },
      { isSome: Bool(false), value: Field(0) },
    ];
    this.emitEvent("addValue", new ZKStateEvent({ addValue, address }));
  }*/
}
