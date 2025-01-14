package ss.tictactoe.model;

import java.util.ArrayList;
import java.util.List;

public class TicTacToeGame implements Game {
    Board board = new Board();
    public Player player1;     //XX
    public Player player2;     //OO
    public Player current= player1;

    @Override
    public boolean isGameover() {
        return board.gameOver();
    }

    @Override
    public Player getTurn() {
        return current;
    }

    @Override
    public Player getWinner() {
        if (board.isWinner(Mark.XX)){
            return player1;} else if (board.isWinner(Mark.OO)) {
            return player2;} else {
            return null;
        }
    }

    @Override
    public List<? extends Move> getValidMoves() {
        List<Move> val = new ArrayList<>();
        for (int i = 0; i < Board.DIM * Board.DIM; i++){
            TicTacToeMove newMove = new TicTacToeMove(Mark.XX, i);
            if (isValidMove(newMove)){
                val.add(newMove);
            }
        }
        for (int i = 0;  i < Board.DIM * Board.DIM; i++){
            TicTacToeMove newMove = new TicTacToeMove(Mark.OO, i);
            if (isValidMove(newMove)){
                val.add(newMove);
            }
        }
        return val;
    }

    @Override
    public boolean isValidMove(Move move) {
        return move.getLocation()>=0 && move.getLocation() < Board.DIM*Board.DIM && board.getField(move.getLocation()) == Mark.EMPTY && move.getMark() == getTurn().getMark();
    }

    @Override
    public void doMove(Move move) {
        board.setField(move.getLocation(), move.getMark());
        if (current == player1){
            current = player2;
        } else {
            current = player1;

        }

    }

    public Game deepCopy() {
        TicTacToeGame newGame = new TicTacToeGame();
        newGame.board = this.board.deepCopy();
        newGame.player1 = this.player1;
        newGame.player2 = this.player2;
        newGame.current = this.current;
        return newGame;
    }
    @Override
    public String toString() {
        return board.toString() +"\n" + current.toString();
    }
    public Board getBoard(){return board;}
}
