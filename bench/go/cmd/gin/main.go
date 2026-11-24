// gin with no kernel: decodes the JSON body and replies with a JSON value.
package main

import (
	"log"
	"net/http"
	"os"

	"github.com/gin-gonic/gin"
)

func main() {
	gin.SetMode(gin.ReleaseMode)
	router := gin.New()
	router.POST("/rpc", func(c *gin.Context) {
		var body map[string]any
		if err := c.ShouldBindJSON(&body); err != nil {
			c.String(http.StatusBadRequest, err.Error())
			return
		}
		c.JSON(http.StatusOK, gin.H{"value": 6})
	})
	log.Fatal(router.Run(os.Getenv("BENCH_LISTEN")))
}
