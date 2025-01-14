package ss.tictactoe.model;

public class TicTacToeMove implements Move {
    Mark mark;
    int location ;

    public TicTacToeMove(Mark mark, int location){
        this.mark = mark;
        this.location = location;
    }

    public Mark getMark(){
        return this.mark;
    }

    public int getLocation(){
        return this.location;
    }
}
