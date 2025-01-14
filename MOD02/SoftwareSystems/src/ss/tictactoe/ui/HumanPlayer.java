package ss.tictactoe.ui;

import java.util.Scanner;
import ss.tictactoe.model.*;

public class HumanPlayer extends AbstractPlayer {
    /**
     * Creates a new Player object.
     *
     * @param name
     */
    public HumanPlayer(String name, Mark mark) {
        super(name, mark);

    }

    @Override
    public Move determineMove(Game game) {
        System.out.println("Enter your move: ");
        while (true){
            Scanner in = new Scanner(System.in);
            String input  = in.nextLine();
            String[] split = input.split("\\s+");
            if ((split.length == 2) &&(getMark().toString()).contains(split[0].toUpperCase())){
                TicTacToeMove move = new TicTacToeMove(getMark(), Integer.parseInt(split[1]));

                if (game.isValidMove(move)){
                    //                game.doMove(move);
                    return move;
                }
            }
            System.out.println("Wrong move, please try again: ");
        }

    }
}
