package ss.project.game.ui;

import java.util.Scanner;
import ss.project.game.ai.ComputerPlayer;
import ss.project.game.ai.StrategyLvlHard;
import ss.project.game.ai.StrategyLvlNormal;
import ss.project.game.model.*;

/**
 * Allows user to play the DotesAndBoxes game. Mainly is used for local games,
 * but its constructor is also used on a server to set the game and players.
 */

public class DnBTUI {
    private GameDnB game;
    /**
     * Constructs a new DnBTUI with the specified DnB
     * game instance and sets the players for the game.
     * @param game The DnB game, which will be played.
     * @param player1 the first player (Blue)
     * @param player2 the second player (Red)
     */
    public DnBTUI(GameDnB game, Player player1, Player player2){
        this.game = game;
        game.player1 = player1;
        game.player2 = player2;
        game.current = game.player1;
    }

    /**
     * Returns the current game. Is needed on the server to get a game with the specified players.
     * @return the current game
     */
    public GameDnB getGame() {
        return game;
    }

    /**
     * Runs the DnB game loop in the console,allowing players play the game until it is interrupted.
     * During each game, while it is not over, allows players to take turns
     * (play the DotsAndBoxes game)
     */
    private void run(){
        while (true){
            game.current = game.player1;
            while (!game.isGameover()){
                System.out.println(game.toString());        // prints state of the current game
                Move currentMove = game.current.determineMove(game);
                game.doMove(currentMove);
            }
            Player winner = game.getWinner();
//             shows the final board state and who is a winner, unless it is a draw.
            if (winner == null){
                System.out.println(game.getBoard().createBoard());
                System.out.println("DRAW!");
            } else {
                System.out.println(game.getBoard().createBoard());
                System.out.println("WINNER: " + winner.getColour() + winner.getName()+ Components.RESET);
            }
//             allows to play another game

            System.out.println("Type \"break\" to interrupt the game, or anything else to continue");
            Scanner in = new Scanner(System.in);
            String command = in.nextLine();
            if (command.equalsIgnoreCase("break")){
                break;
            }
            game.getBoard().reset();
        }
    }

    /**
     * Ask user to input names of both players,
     * then creates new instance of GameDnB and two HumanPlayers (or ComputerPlayers),
     * then creates new instance of DnBTui and runs it.
     */
    public static void main(String[] args) {
        System.out.println("Player 1: ");
        Scanner in = new Scanner(System.in);
        String player1_name = in.nextLine();
        System.out.println("Player 2: ");
        String player2_name = in.nextLine();
        GameDnB gameDnB = new GameDnB();
        //here you can choose which player will be AI by changing players
        Player player1 = new ComputerPlayer(Components.BLUE, new StrategyLvlHard());
        Player player2 = new ComputerPlayer(Components.RED, new StrategyLvlNormal());
        //        Player player1 = new HumanPlayer(player1_name, Components.BLUE);
        //        Player player2 = new HumanPlayer(player2_name, Components.RED);
        DnBTUI tui = new DnBTUI(gameDnB,player1,player2);
        tui.run();
    }
}
