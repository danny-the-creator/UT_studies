/**
 * Network Systems Challenge 1: Playing with bits
 * v0.3
 * © 2023, DACS University of Twente
 * 
 * Note: 
 * Java only has signed integers. For this assignment (and other assignments in the coming weeks) 
 * this means you have to be carefull while shifting numbers with the most significant bit set to 1 to the right.
 * You should use java's unsigned right shift (>>>) instead of the 'normal' shift (>>).
 */

public class Check {

    // Put which exercise you're currently doing here, you can also input is as the first argument when running the program
    private String whichexercise = "3d";

    // -------- write your code in this function --------------------
    static int your_function(int x, int y) {

//        return 8;   ex 1
//        return 1 << x;  ex 2
//        return 1<<x | y; ex 3
//        return ~(1<<x) & y; ex 4
//        return ((0b1000 & x) >> 3) + 1; ex 5
//        return (((1<<y) & x) >>> y ) + ((((1<<y) & x) >>> y ) << 3) + ((((1<<y) & x) >>> y ) << 4);

//        return 0b1111000; ex 1
//        return 0b1111 & x; ex 2
//        return (1<<x) -1; ex 3
//        return ((1 << y) -1) & x; ex 4
//        return x >>> y & 0b11111111; ex 5
//        return x ^ 0b110001; ex 6

//        return (y<<8) + x;
//        return (x>>>24) & 0b1111;
//        return ((((1 << 31)-1)&(~(x >>> 10 ^ y >>> 10))) + 1)>>>31;

//        return Integer.reverse(x);
//        return ((x >>> 24 & 0xff ))|((x << 8) & 0xff0000) | ((x >>> 8) & 0xff00) | ((x << 24) & 0xff000000);






        // note: as you update this function for later exercises, we advise
        // you to not erase your earlier answers, but comment them out so you
        // can have a look at them again later.

    }
    // -------- end of your code -------------------


    int eval(String excs, int x, int y) {
        // System.out.printf("Eval: %s | %d | %d\n", excs, x, y);
        char[] exc = excs.toCharArray();
        int i=0;
        while (exc[i]!=';') i++; 
        i++;
        int[] z = new int[16];
        int sp=-1;
        while (i < exc.length) {
            switch (exc[i]) {
                case 'a': z[++sp]=x; break;
                case 'b': z[++sp]=y; break;
                case 'd': z[sp+1]=z[sp]; sp++; break;
                case '~': z[sp]=~z[sp]; break;
                case '>': sp--; z[sp]=z[sp]>>>z[sp+1]; break;
                case '<': sp--; z[sp]=z[sp]<<z[sp+1]; break;
                case '+': sp--; z[sp]+=z[sp+1]; break;
                case '-': sp--; z[sp]-=z[sp+1]; break;
                case '|': sp--; z[sp]|=z[sp+1]; break;
                case '&': sp--; z[sp]&=z[sp+1]; break;
                case '^': sp--; z[sp]^=z[sp+1]; break;
                case '=': sp--; if (z[sp+1]==z[sp]){ z[sp]=1; } else { z[sp]=0; } break;
                case '?': sp-=2; if (z[sp+2] == 0) z[sp]=z[sp+1]; break;
                case ' ': break;
                default: z[++sp]=exc[i]-'0';
            }
            // {System.out.printf("op: %c  z:",exc[i]); for (int j=0;j<=sp;j++) System.out.printf(" 0x%02x",z[j]); System.out.printf("\n");}
            i++;
        }
        return z[0];
    }

    private String exercises[] = { 
        "1a:1;8",
        "1b:1;1a<", 
        "1c:3;1a<b|", 
        "1d:3;1a<~b&", 
        "1e:1;a3>1&1+",
        "1f:2;62<1+0ab>1&?",
      
        "2a:1;69+3<", 
        "2b:1;a78+&", 
        "2c:1;1a<1-", 
        "2d:2;1b<1-a&", 
        "2e:2;ab>18<1-&", 
        "2f:1;34<1+a^", 
      
        "3a:4;b8<a|",
        "3b:1;a62<>78+&",
        "3c:;ab^5>5>0=",
        "3d:1;a888++>a8<888++>8<a88+<888++>88+<a888++<|||"
    };

    public int test(){
        String exercise = whichexercise;
        int nexercises = exercises.length;
        int e;
        for (e=0;e<nexercises;e++) if (exercises[e].split(":")[0].equals(exercise)) break;
        if (e==nexercises) { System.out.printf("Exercise \"%s\" not found!\n", whichexercise); return 1; }
     
        int i=0;
        while (exercises[e].toCharArray()[i]!=':') i++;
        i++;
        int amax=512;
        int bmax=512;
        char whattest=exercises[e].toCharArray()[i];
        switch (whattest) { 
           case '1': bmax=0; break;      // 1 input (is always x)
           case '2': bmax=31; break;      // y is bit count
           case '3': amax=31; break;      // x is bit count
           case '4': amax=255; bmax=255; break;      // x and y are both bytes
        }
        for (int b=0;b<=bmax;b++) 
           for (int a=0;a<=amax;a++)
           {
              int x=a;
              if (a>255) x*=13+17*0x100+23*0x10000+0x1000000;
              int y=b;
              if (b>255) y*=11+19*0x100+29*0x10000+0x1000000;
              int r=your_function(x,y);
              int s=eval(exercises[e],x,y);
              if (r!=s) {
                 switch (whattest) {
                    case '1': System.out.printf("Your function is incorrect for x = %d = 0x%08x:\nit returned %d = 0x%08x, while the correct answer is %d = 0x%08x.\n", x,x, r,r, s,s); break;
                    default: System.out.printf("Your function is incorrect for x = %d = 0x%08x, y = %d = 0x%08x:\nit returned %d = 0x%08x, while the correct answer is %d = 0x%08x.\n", x,x, y,y, r,r, s,s); break;
                 }
                 return 1;
              }
           }
        System.out.printf("Your function for exercise "+whichexercise+" is correct; congratulations%s!\n", (e==nexercises-1) ? " on completing the final exercise" : "");
        return 0;
    }

    private Check(String whichexercise) {
        this.whichexercise = whichexercise.toLowerCase();
    }

    private Check(){}

    public static void main(String args[]){
        Check checker = null;
        if (args.length == 1) {
            checker = new Check(args[0]);
        } else {
            checker = new Check();
        }
        checker.test();
    }
}
