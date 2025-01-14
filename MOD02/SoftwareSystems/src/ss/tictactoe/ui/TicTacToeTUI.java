package ss.tictactoe.ui;

import java.util.Scanner;
import ss.tictactoe.ai.ComputerPlayer;
import ss.tictactoe.ai.NaiveStrategy;
import ss.tictactoe.ai.SmartStrategy;
import ss.tictactoe.model.*;


public class TicTacToeTUI {
    private TicTacToeGame game;
    public  TicTacToeTUI(TicTacToeGame game){
        this.game = game;
    }
    public static void main(String[] args) {
        TicTacToeGame game = new TicTacToeGame();
        TicTacToeTUI tui = new TicTacToeTUI(game);
        tui.run();
    }

    /**
     * Runs TicTacToe game
     */
    private void run() {
        System.out.println("Player 1: ");
        Scanner in = new Scanner(System.in);
        String player1_name = in.nextLine();
        System.out.println("Player 2: ");
        String player2_name = in.nextLine();
        game = new TicTacToeGame();
        if (player1_name.equals("-N")){
            game.player1 = new ComputerPlayer(Mark.XX, new NaiveStrategy());
        } else if (player1_name.equals("-S")){
            game.player1 = new ComputerPlayer(Mark.XX, new SmartStrategy());
        } else { game.player1  = new HumanPlayer(player1_name, Mark.XX); }
        if (player2_name.equals("-N")) {
            game.player2 = new ComputerPlayer(Mark.OO, new NaiveStrategy());
        } else if (player2_name.equals("-S")) {
            game.player2 = new ComputerPlayer(Mark.OO, new SmartStrategy());
        } else { game.player2 = new HumanPlayer(player2_name, Mark.OO); }
        game.current = game.player1;
        while (true) {
            while (!game.isGameover()) {
                System.out.println(game.toString());
                Move currentMove = game.current.determineMove(game);
                game.doMove(currentMove);
            }
            if (game.getWinner() == null){
                System.out.println("DRAW");
                System.out.println(game.toString().replace("Player "+game.current.getName(), ""));
            } else {
                System.out.println("WINNER: " +game.getWinner().getName());
                System.out.println(game.toString()+ " is Loser!");
            }

            System.out.println("Do you want to continue (Yes/No)?");
            String command = in.nextLine();
            if (command.toLowerCase().equals("no")){
                break;
            }
            game.getBoard().reset();

        }
    }
}
